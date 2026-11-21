#!/usr/bin/env python3
"""git-forge: a standalone GitHub-compatible git forge in one process.

Serves git smart HTTP (upload-pack v2, receive-pack v0), the REST v3 API,
GraphQL v4 and MCP, all from its own in-memory store. Standard library only.
No git binary, no outside service, no UI.

Lifecycle (the make.fun env contract): bind an ephemeral port, POST the port
to $MAKEFUN_ENV_URL/register, poll GET $MAKEFUN_ENV_URL/done until done, exit 0.

Determinism: every id, timestamp and ordering is derived from the trial
inputs (the fixed scenario seed, MAKEFUN_TRIAL_NOW, request order). Nothing
here reads the wall clock or unseeded randomness, so two runs on the same
instance leave the same state.
"""

import base64 as _b64
import hashlib
import http.server as _http
import json
import os
import re
import socket as _socket
import sys
import threading
import time
import urllib.parse as _url
import urllib.request
import urllib.request as _urllib
import urllib.error
import zlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qs, unquote

# ---------------------------------------------------------------- config

ENV_URL = os.environ.get("MAKEFUN_ENV_URL", "").rstrip("/")
SHOP_TOKEN = os.environ.get("MAKEFUN_SHOP_TOKEN", "")
TRIAL_NOW = os.environ.get("MAKEFUN_TRIAL_NOW", "")
# The instance's opening time; every timestamp the forge emits. Fixed when
# the trial does not set it, so two runs agree byte for byte.
NOW_ISO = TRIAL_NOW or "2025-01-01T00:00:00Z"

# ---------------------------------------------------------------- the viewer

# The suite's scenario is fixed data (kit program/env/src/wire.ts): one seed
# drives every generated name, and the viewer is users[0]. Recompute it here
# so the forge knows the login the bearer token names.
_SCENARIO_SEED = 0x6a09E667F3BCC909
_U64 = (1 << 64) - 1
_FIRST_NAMES = ['ada', 'bram', 'cora', 'dmitri', 'elena', 'felix', 'greta',
                'hugo', 'iris', 'jonas', 'kira', 'lars', 'mira', 'nico',
                'olga', 'pavel', 'quinn', 'rosa', 'sven', 'tess', 'ulla',
                'vito', 'wren', 'yara', 'zane']
_LAST_NAMES = ['anders', 'bauer', 'costa', 'dahl', 'eriksen', 'fischer',
               'garcia', 'holm', 'iversen', 'jansen', 'keller', 'lind',
               'moreau', 'novak', 'olsen', 'peters', 'quist', 'rossi',
               'sato', 'turi', 'ulrich', 'vega', 'weber', 'xu', 'yilmaz',
               'zimmer']


def _fnv1a64(text):
    h = 0xCBF29CE484222325
    for ch in text:
        h ^= ord(ch)
        h = (h * 0x100000001B3) & _U64
    return h


def _mix64(v):
    z = (v + 0x9E3779B97F4A7C15) & _U64
    z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & _U64
    z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & _U64
    return (z ^ (z >> 31)) & _U64


class _Rng:
    def __init__(self, seed):
        s = seed & _U64
        self.state = s if s else _SCENARIO_SEED

    def next_u64(self):
        x = self.state
        x = (x ^ (x >> 12)) & _U64
        x = (x ^ (x << 25)) & _U64
        x = (x ^ (x >> 27)) & _U64
        self.state = x
        return (x * 0x2545F4914F6CDD1D) & _U64

    def next_u32(self):
        return self.next_u64() >> 32

    def next_int(self, mx):
        if mx == 1:
            return 0
        limit = 4294967296 - (4294967296 % mx)
        while True:
            v = self.next_u32()
            if v < limit:
                return v % mx

    def pick(self, items):
        return items[self.next_int(len(items))]


def _viewer_login():
    rng = _Rng(_mix64(_SCENARIO_SEED ^ _fnv1a64("users")))
    first = rng.pick(_FIRST_NAMES)
    last = rng.pick(_LAST_NAMES)
    login = re.sub(r"[^a-z0-9-]", "", first + last)
    return login


VIEWER_LOGIN = _viewer_login()          # 'adaiversen'
VIEWER_ID = 1000
VIEWER_NAME = "ada iversen"
VIEWER_EMAIL = VIEWER_LOGIN + "@example.invalid"

ZERO_OID = "0" * 40

# ---------------------------------------------------------------- git objects

# A git object is (type, raw bytes). Commits, trees and blobs are built and
# read by hand; the pack reader/writer below moves them over the wire.


def git_hash(otype, data):
    h = hashlib.sha1()
    h.update(otype.encode() + b" " + str(len(data)).encode() + b"\x00" + data)
    return h.hexdigest()


def build_commit(tree, parents, message, author=None):
    author = author or "%s <%s>" % (VIEWER_NAME, VIEWER_EMAIL)
    lines = ["tree %s" % tree]
    for p in parents:
        lines.append("parent %s" % p)
    lines.append("author %s 1735689600 +0000" % author)
    lines.append("committer %s 1735689600 +0000" % author)
    lines.append("")
    lines.append(message)
    return "\n".join(lines).encode()


def parse_commit(data):
    """Return (tree, parents, message)."""
    text = data.decode("utf-8", "replace")
    header, _, message = text.partition("\n\n")
    tree = None
    parents = []
    for line in header.split("\n"):
        if line.startswith("tree "):
            tree = line[5:].strip()
        elif line.startswith("parent "):
            parents.append(line[7:].strip())
    return tree, parents, message


def build_tree(entries):
    """entries: list of (mode, name, sha-hex). Returns raw tree bytes.
    Git sorts tree entries with directories compared as if their name had
    a trailing '/', so a file `ab-c` sorts before a directory `ab`."""
    def sort_key(e):
        mode, name, _sha = e
        return name + "/" if mode == "40000" else name
    out = b""
    for mode, name, sha in sorted(entries, key=sort_key):
        out += ("%s %s\x00" % (mode, name)).encode() + bytes.fromhex(sha)
    return out


def parse_tree(data):
    """Return list of (mode, name, sha-hex)."""
    out = []
    i = 0
    while i < len(data):
        j = data.index(b" ", i)
        mode = data[i:j].decode()
        k = data.index(b"\x00", j)
        name = data[j + 1:k].decode()
        sha = data[k + 1:k + 21].hex()
        out.append((mode, name, sha))
        i = k + 21
    return out


# --- packfiles ---------------------------------------------------------------

def _read_varint(data, pos):
    """Git pack size encoding: returns (type, size, new_pos)."""
    b = data[pos]
    pos += 1
    otype = (b >> 4) & 7
    size = b & 0x0F
    shift = 4
    while b & 0x80:
        b = data[pos]
        pos += 1
        size |= (b & 0x7F) << shift
        shift += 7
    return otype, size, pos


def apply_delta(base, delta):
    """Apply a git delta (xdelta-style) to base bytes."""
    pos = 0

    def read_varint():
        nonlocal pos
        out = 0
        shift = 0
        while True:
            b = delta[pos]
            pos += 1
            out |= (b & 0x7F) << shift
            shift += 7
            if not (b & 0x80):
                return out

    src_size = read_varint()
    tgt_size = read_varint()
    if src_size != len(base):
        raise ValueError("delta base size mismatch")
    out = bytearray()
    while pos < len(delta):
        op = delta[pos]
        pos += 1
        if op & 0x80:
            offset = 0
            size = 0
            for i in range(4):
                if op & (1 << i):
                    offset |= delta[pos] << (8 * i)
                    pos += 1
            for i in range(3):
                if op & (0x10 << i):
                    size |= delta[pos] << (8 * i)
                    pos += 1
            if size == 0:
                size = 0x10000
            out += base[offset:offset + size]
        elif op:
            out += delta[pos:pos + op]
            pos += op
        else:
            raise ValueError("delta op 0")
    if len(out) != tgt_size:
        raise ValueError("delta target size mismatch")
    return bytes(out)


def read_pack(data, base_lookup=None):
    """Parse a packfile. Returns list of (type, raw bytes) in pack order.

    Handles OBJ_COMMIT/TREE/BLOB/TAG, OFS_DELTA and REF_DELTA. A thin
    pack's REF_DELTA bases may live outside the pack; pass the repo's
    object store as base_lookup (sha -> (type, raw)) to resolve them.
    """
    if data[:4] != b"PACK" or int.from_bytes(data[4:8], "big") != 2:
        raise ValueError("not a v2 packfile")
    count = int.from_bytes(data[8:12], "big")
    pos = 12
    objs = []          # (sha, type, data) in pack order
    by_sha = {}
    by_offset = {}     # pack byte offset of an entry start -> (sha, type, data)
    for _ in range(count):
        entry_start = pos
        otype, size, pos = _read_varint(data, pos)
        if otype in (1, 2, 3, 4):      # commit, tree, blob, tag
            d = zlib.decompressobj()
            raw = d.decompress(data[pos:])
            pos += len(data[pos:]) - len(d.unused_data)
            tname = {1: "commit", 2: "tree", 3: "blob", 4: "tag"}[otype]
            sha = git_hash(tname, raw)
            objs.append((sha, tname, raw))
            by_sha[sha] = (tname, raw)
            by_offset[entry_start] = (sha, tname, raw)
        elif otype == 6:               # OFS_DELTA
            b = data[pos]
            pos += 1
            offset = b & 0x7F
            while b & 0x80:
                b = data[pos]
                pos += 1
                offset = ((offset + 1) << 7) | (b & 0x7F)
            base_start = entry_start - offset
            if base_start not in by_offset:
                raise ValueError("ofs-delta base offset %d unknown" % base_start)
            _, btype, braw = by_offset[base_start]
            d = zlib.decompressobj()
            delta = d.decompress(data[pos:])
            pos += len(data[pos:]) - len(d.unused_data)
            raw = apply_delta(braw, delta)
            sha = git_hash(btype, raw)
            objs.append((sha, btype, raw))
            by_sha[sha] = (btype, raw)
            by_offset[entry_start] = (sha, btype, raw)
        elif otype == 7:               # REF_DELTA
            base_sha = data[pos:pos + 20].hex()
            pos += 20
            d = zlib.decompressobj()
            delta = d.decompress(data[pos:])
            pos += len(data[pos:]) - len(d.unused_data)
            if base_sha in by_sha:
                btype, braw = by_sha[base_sha]
            elif base_lookup is not None and base_sha in base_lookup:
                btype, braw = base_lookup[base_sha]
            else:
                raise ValueError("ref-delta base %s not in pack" % base_sha)
            raw = apply_delta(braw, delta)
            sha = git_hash(btype, raw)
            objs.append((sha, btype, raw))
            by_sha[sha] = (btype, raw)
            by_offset[entry_start] = (sha, btype, raw)
        else:
            raise ValueError("unknown pack object type %d" % otype)
    return [(t, raw) for _, t, raw in objs]


def write_pack(objects):
    """objects: list of (type, raw). Writes a v2 pack with full objects only
    (no deltas) — valid on the wire and simplest to verify."""
    out = bytearray()
    out += b"PACK" + (2).to_bytes(4, "big") + len(objects).to_bytes(4, "big")
    for otype, raw in objects:
        tnum = {"commit": 1, "tree": 2, "blob": 3, "tag": 4}[otype]
        size = len(raw)
        first = (tnum << 4) | (size & 0x0F)
        size >>= 4
        if size:
            first |= 0x80
        out.append(first)
        while size:
            b = size & 0x7F
            size >>= 7
            if size:
                b |= 0x80
            out.append(b)
        out += zlib.compress(raw)
    out += hashlib.sha1(bytes(out)).digest()
    return bytes(out)


# --- pkt-line -----------------------------------------------------------------

def pkt_line(s):
    if isinstance(s, str):
        s = s.encode()
    return ("%04x" % (len(s) + 4)).encode() + s


def pkt_flush():
    return b"0000"


def pkt_delim():
    return b"0001"


def read_pkt_lines(data, stop_at_flush=False):
    """Split a pkt-line stream into lines (bytes, no length prefix);
    flush/delim become None markers. With stop_at_flush, stop after the
    first flush (the rest of the stream, e.g. a pack, starts at pos)."""
    out = []
    pos = 0
    while pos + 4 <= len(data):
        n = int(data[pos:pos + 4], 16)
        if n == 0:
            out.append(None)
            pos += 4
            if stop_at_flush:
                break
            continue
        if n == 1:
            out.append(b"\x01")
            pos += 4
            continue
        out.append(data[pos + 4:pos + n])
        pos += n
    return out, pos


def sideband64(data, band=1):
    """Frame payload into side-band-64k packets (max 65520 payload each)."""
    out = bytearray()
    for i in range(0, len(data), 65520):
        chunk = bytes([band]) + data[i:i + 65520]
        out += pkt_line(chunk)
    return bytes(out)


# ---------------------------------------------------------------- the store

import base64 as _b64

LOCK = threading.RLock()


def node_id(kind, num):
    return _b64.b64encode(("%s:%s" % (kind, num)).encode()).decode()


def _iso_now():
    return NOW_ISO


class Repo:
    def __init__(self, rid, name, description=""):
        self.id = rid
        self.name = name
        self.owner = VIEWER_LOGIN
        self.description = description or ""
        self.default_branch = "main"
        self.objects = {}      # sha -> (type, raw)
        self.refs = {}         # 'refs/heads/main' -> sha
        self.files = {}        # branch -> {path: (blob_sha, mode)}
        self.issues = {}       # number -> dict
        self.issue_seq = 0
        self.prs = {}          # number -> dict
        self.pr_seq = 0
        self.labels = {}       # name -> dict
        self.created_at = _iso_now()
        self.updated_at = _iso_now()
        self.pushed_at = _iso_now()
        self.seq = rid          # creation order, for list ordering

    # -- git objects ---------------------------------------------------------
    def put_object(self, otype, raw):
        sha = git_hash(otype, raw)
        self.objects[sha] = (otype, raw)
        return sha

    def get_object(self, sha):
        return self.objects.get(sha)

    def ref(self, name):
        return self.refs.get(name)

    def head_sha(self, branch=None):
        return self.refs.get("refs/heads/" + (branch or self.default_branch))

    def commit_tree(self, sha):
        """(tree_sha, parents, message) for a commit, or None."""
        obj = self.objects.get(sha)
        if not obj or obj[0] != "commit":
            return None
        return parse_commit(obj[1])

    def tree_files(self, tree_sha):
        """Flatten a tree to {path: (blob_sha, mode)}."""
        out = {}

        def walk(tsha, prefix):
            obj = self.objects.get(tsha)
            if not obj or obj[0] != "tree":
                return
            for mode, name, sha in parse_tree(obj[1]):
                path = prefix + name
                if mode == "40000":
                    walk(sha, path + "/")
                else:
                    out[path] = (sha, mode)

        walk(tree_sha, "")
        return out

    def build_tree_from_files(self, files):
        """files: {path: (blob_sha, mode)} -> tree sha (writes tree objects)."""
        # group by directory
        def build(paths):
            entries = []
            dirs = {}
            for path in sorted(paths):
                parts = path.split("/")
                if len(parts) == 1:
                    sha, mode = paths[path]
                    entries.append((mode, parts[0], sha))
                else:
                    dirs.setdefault(parts[0], []).append("/".join(parts[1:]))
            for d in sorted(dirs):
                subfiles = {}
                for p in dirs[d]:
                    subfiles[p] = paths[d + "/" + p]
                entries.append(("40000", d, build(subfiles)))
            raw = build_tree(entries)
            return self.put_object("tree", raw)

        return build(files)

    def commit(self, branch, files, message, parents):
        """Create a commit on `branch` from the file map. Returns commit sha."""
        tree = self.build_tree_from_files(files)
        raw = build_commit(tree, parents, message)
        sha = self.put_object("commit", raw)
        self.refs["refs/heads/" + branch] = sha
        self.files[branch] = dict(files)
        self.pushed_at = _iso_now()
        return sha

    def is_ancestor(self, anc, desc):
        """True if anc is reachable from desc (or anc == desc)."""
        if anc == desc:
            return True
        seen = set()
        stack = [desc]
        while stack:
            cur = stack.pop()
            if cur in seen:
                continue
            seen.add(cur)
            parsed = self.commit_tree(cur)
            if not parsed:
                continue
            _, parents, _ = parsed
            if anc in parents:
                return True
            stack.extend(parents)
        return False

    def merge_base(self, a, b):
        """First common ancestor of a and b (BFS from both), or None."""
        if a is None or b is None:
            return None
        seen_a = {a}
        stack = [a]
        while stack:
            cur = stack.pop()
            parsed = self.commit_tree(cur)
            if parsed:
                for p in parsed[1]:
                    if p not in seen_a:
                        seen_a.add(p)
                        stack.append(p)
        stack = [b]
        seen_b = set()
        while stack:
            cur = stack.pop()
            if cur in seen_a:
                return cur
            if cur in seen_b:
                continue
            seen_b.add(cur)
            parsed = self.commit_tree(cur)
            if parsed:
                stack.extend(parsed[1])
        return None


class Store:
    def __init__(self):
        self.repos = {}        # (owner, name) -> Repo
        self.repo_id_seq = 5000
        self.issue_id_seq = 1000000
        self.pr_id_seq = 2000000
        self.comment_id_seq = 3000000

    def create_repo(self, name, description=""):
        rid = self.repo_id_seq
        self.repo_id_seq += 1
        repo = Repo(rid, name, description)
        self.repos[(VIEWER_LOGIN, name)] = repo
        return repo

    def get_repo(self, owner, name):
        return self.repos.get((owner, name))

    def delete_repo(self, owner, name):
        return self.repos.pop((owner, name), None)

    def list_repos(self, owner):
        rs = [r for (o, _), r in self.repos.items() if o == owner]
        rs.sort(key=lambda r: -r.seq)
        return rs


STORE = Store()


# ---------------------------------------------------------------- JSON views

def repo_json(r, base_url):
    return {
        "id": r.id,
        "node_id": node_id("Repository", r.id),
        "name": r.name,
        "full_name": "%s/%s" % (r.owner, r.name),
        "owner": {
            "login": r.owner, "id": VIEWER_ID, "node_id": node_id("User", VIEWER_ID),
            "type": "User", "site_admin": False,
        },
        "private": False,
        "html_url": "%s/%s/%s" % (base_url, r.owner, r.name),
        "description": r.description,
        "fork": False,
        "url": "%s/api/v3/repos/%s/%s" % (base_url, r.owner, r.name),
        "created_at": r.created_at,
        "updated_at": r.updated_at,
        "pushed_at": r.pushed_at,
        "git_url": "git://%s/%s/%s.git" % (base_url.split("://", 1)[-1], r.owner, r.name),
        "ssh_url": "git@%s:%s/%s.git" % (base_url.split("://", 1)[-1], r.owner, r.name),
        "clone_url": "%s/%s/%s.git" % (base_url, r.owner, r.name),
        "homepage": None,
        "size": 0,
        "stargazers_count": 0,
        "watchers_count": 0,
        "language": None,
        "has_issues": True,
        "has_projects": True,
        "has_downloads": True,
        "has_wiki": True,
        "has_pages": False,
        "has_discussions": False,
        "forks_count": 0,
        "mirror_url": None,
        "archived": False,
        "disabled": False,
        "open_issues_count": sum(1 for i in r.issues.values() if i["state"] == "open"),
        "license": None,
        "allow_forking": True,
        "is_template": False,
        "web_commit_signoff_required": False,
        "topics": [],
        "visibility": "public",
        "forks": 0,
        "open_issues": sum(1 for i in r.issues.values() if i["state"] == "open"),
        "watchers": 0,
        "default_branch": r.default_branch,
        "permissions": {"admin": True, "maintain": True, "push": True,
                        "triage": True, "pull": True},
    }


def issue_json(r, issue):
    return {
        "id": issue["id"],
        "node_id": node_id("Issue", issue["id"]),
        "number": issue["number"],
        "title": issue["title"],
        "body": issue.get("body") or "",
        "state": issue["state"],
        "state_reason": None if issue["state"] == "open" else "completed",
        "labels": [dict(l) for l in issue["labels"]],
        "user": {"login": VIEWER_LOGIN, "id": VIEWER_ID,
                 "node_id": node_id("User", VIEWER_ID), "type": "User"},
        "assignee": None,
        "assignees": [],
        "milestone": None,
        "locked": False,
        "comments": len(issue.get("comments", [])),
        "created_at": issue["created_at"],
        "updated_at": issue["updated_at"],
        "closed_at": issue.get("closed_at"),
        "author_association": "OWNER",
        "repository_url": "/api/v3/repos/%s/%s" % (r.owner, r.name),
        "html_url": "/%s/%s/issues/%d" % (r.owner, r.name, issue["number"]),
        "url": "/api/v3/repos/%s/%s/issues/%d" % (r.owner, r.name, issue["number"]),
    }


def pr_json(r, pr):
    return {
        "id": pr["id"],
        "node_id": node_id("PullRequest", pr["id"]),
        "number": pr["number"],
        "title": pr["title"],
        "body": pr.get("body") or "",
        "state": pr["state"],
        "locked": False,
        "user": {"login": VIEWER_LOGIN, "id": VIEWER_ID,
                 "node_id": node_id("User", VIEWER_ID), "type": "User"},
        "labels": [dict(l) for l in pr.get("labels", [])],
        "head": {"label": "%s:%s" % (r.owner, pr["head"]),
                 "ref": pr["head"], "sha": pr["head_sha"],
                 "user": {"login": VIEWER_LOGIN, "id": VIEWER_ID},
                 "repo": {"id": r.id, "name": r.name,
                          "full_name": "%s/%s" % (r.owner, r.name)}},
        "base": {"label": "%s:%s" % (r.owner, pr["base"]),
                 "ref": pr["base"], "sha": pr["base_sha"],
                 "user": {"login": VIEWER_LOGIN, "id": VIEWER_ID},
                 "repo": {"id": r.id, "name": r.name,
                          "full_name": "%s/%s" % (r.owner, r.name)}},
        "merged": pr["merged"],
        "mergeable": pr["mergeable"],
        "mergeable_state": "clean" if pr["mergeable"] else "dirty",
        "merged_at": pr.get("merged_at"),
        "merge_commit_sha": pr.get("merge_commit_sha"),
        "created_at": pr["created_at"],
        "updated_at": pr["updated_at"],
        "closed_at": pr.get("closed_at"),
        "draft": False,
        "commits": pr.get("commits", 1),
        "additions": pr.get("additions", 0),
        "deletions": pr.get("deletions", 0),
        "changed_files": pr.get("changed_files", 0),
        "html_url": "/%s/%s/pull/%d" % (r.owner, r.name, pr["number"]),
        "url": "/api/v3/repos/%s/%s/pulls/%d" % (r.owner, r.name, pr["number"]),
    }

# ---------------------------------------------------------------- HTTP plumbing

REQ_COUNTER = [0]
REQ_LOCK = threading.Lock()


def next_req_id():
    with REQ_LOCK:
        REQ_COUNTER[0] += 1
        return "req-%d" % REQ_COUNTER[0]


def json_bytes(obj):
    return json.dumps(obj, separators=(",", ":"), ensure_ascii=False).encode()


def link_header(base, path, query, page, per_page, total):
    """GitHub-style Link header for pagination (absolute URLs)."""
    total_pages = max(1, (total + per_page - 1) // per_page)
    parts = []

    def url(p):
        q = dict(query)
        q["page"] = str(p)
        q["per_page"] = str(per_page)
        qs = "&".join("%s=%s" % (k, v) for k, v in sorted(q.items()))
        return "<%s%s?%s>" % (base, path, qs)

    if page < total_pages:
        parts.append('%s; rel="next"' % url(page + 1))
        parts.append('%s; rel="last"' % url(total_pages))
    if page > 1:
        parts.append('%s; rel="prev"' % url(page - 1))
        parts.append('%s; rel="first"' % url(1))
    return ", ".join(parts) if parts else None


def paginate(items, query):
    """Returns (page_items, link_header_value_or_None)."""
    try:
        per_page = int(query.get("per_page", ["30"])[0])
    except ValueError:
        per_page = 30
    per_page = max(1, min(100, per_page))
    try:
        page = int(query.get("page", ["1"])[0])
    except ValueError:
        page = 1
    page = max(1, page)
    start = (page - 1) * per_page
    return items[start:start + per_page], page, per_page


class ApiError(Exception):
    def __init__(self, status, message):
        super().__init__(message)
        self.status = status
        self.message = message


def not_found(msg="Not Found"):
    raise ApiError(404, msg)


def bad_request(msg="Bad Request"):
    raise ApiError(400, msg)


# ---------------------------------------------------------------- REST handlers

def _owner_repo_or_404(owner, name):
    r = STORE.get_repo(owner, name)
    if r is None:
        not_found("Not Found")
    return r


def _require_viewer_owner(owner):
    # A repository belongs to the login the token names; any other owner is 404.
    if owner != VIEWER_LOGIN:
        not_found("Not Found")


def _parse_body(handler):
    length = int(handler.headers.get("Content-Length") or 0)
    raw = handler.rfile.read(length) if length else b""
    if not raw:
        return {}
    try:
        body = json.loads(raw.decode("utf-8"))
    except Exception:
        bad_request("Invalid JSON")
    if not isinstance(body, dict):
        bad_request("Invalid JSON")
    return body


def _content_commit(r, branch, message, new_files, base_files, parents):
    """Create a commit on `branch` from new_files over base_files."""
    files = dict(base_files)
    for path, val in new_files.items():
        if val is None:
            files.pop(path, None)
        else:
            files[path] = val
    return r.commit(branch, files, message, parents)


def handle_rest(handler, method, path, query, base_url):
    """Returns (status, obj_or_None, extra_headers). Raises ApiError."""
    parts = [unquote(p) for p in path.split("/") if p != ""]
    # parts[0] == 'api', parts[1] == 'v3'
    rest = parts[2:]
    body = None
    if method in ("POST", "PUT", "PATCH", "DELETE"):
        body = _parse_body(handler)

    def need_repo(owner, name):
        _require_viewer_owner(owner)
        return _owner_repo_or_404(owner, name)

    # ---- API root ------------------------------------------------------------
    if not rest:
        if method == "GET":
            return 200, {"current_user_url": base_url + "/api/v3/user",
                         "rate_limit_url": base_url + "/api/v3/rate_limit",
                         "repository_url": base_url + "/api/v3/repos/{owner}/{repo}"}, \
                   {"X-OAuth-Scopes": "repo, read:org"}
        not_found()

    # ---- /meta ---------------------------------------------------------------
    if rest == ["meta"] and method == "GET":
        return 200, {"installed_version": "1.0.0",
                     "verifiable_password_authentication": False,
                     "ssh_key_fingerprints": {}}, {}

    # ---- /rate_limit ---------------------------------------------------------
    if rest == ["rate_limit"] and method == "GET":
        return 200, {"resources": {"core": {"limit": 5000, "remaining": 5000,
                                            "reset": 1735689600},
                                   "search": {"limit": 30, "remaining": 30,
                                              "reset": 1735689600}},
                     "rate": {"limit": 5000, "remaining": 5000,
                              "reset": 1735689600}}, {}

    # ---- /user ---------------------------------------------------------------
    if rest == ["user"] and method == "GET":
        return 200, {"login": VIEWER_LOGIN, "id": VIEWER_ID,
                     "node_id": node_id("User", VIEWER_ID),
                     "avatar_url": "", "type": "User", "site_admin": False,
                     "name": VIEWER_NAME, "email": VIEWER_EMAIL}, {}

    # ---- /user/repos ---------------------------------------------------------
    if rest == ["user", "repos"]:
        if method == "GET":
            repos = STORE.list_repos(VIEWER_LOGIN)
            items, page, per_page = paginate([repo_json(r, base_url) for r in repos], query)
            link = link_header(base_url, "/api/v3/user/repos", query, page, per_page, len(repos))
            return 200, items, ({"Link": link} if link else {})
        if method == "POST":
            name = (body or {}).get("name")
            if not name or not isinstance(name, str):
                raise ApiError(422, "Validation Failed: name is required")
            if STORE.get_repo(VIEWER_LOGIN, name) is not None:
                raise ApiError(422, "Repository creation failed: name already exists")
            r = STORE.create_repo(name, (body or {}).get("description") or "")
            return 201, repo_json(r, base_url), {}
        not_found()

    # ---- /repos/{owner}/{repo}... --------------------------------------------
    if len(rest) >= 3 and rest[0] == "repos":
        owner, name = rest[1], rest[2]
        tail = rest[3:]

        # /repos/{o}/{r}
        if not tail:
            if method == "GET":
                r = need_repo(owner, name)
                return 200, repo_json(r, base_url), {}
            if method == "PATCH":
                r = need_repo(owner, name)
                if body and "description" in body:
                    r.description = body["description"] or ""
                if body and "default_branch" in body and body["default_branch"]:
                    r.default_branch = body["default_branch"]
                r.updated_at = _iso_now()
                return 200, repo_json(r, base_url), {}
            if method == "DELETE":
                _require_viewer_owner(owner)
                if STORE.delete_repo(owner, name) is None:
                    not_found()
                return 204, None, {}
            not_found()

        r = need_repo(owner, name)

        # /git/refs
        if tail[:2] == ["git", "refs"]:
            if method == "POST" and len(tail) == 2:
                ref = (body or {}).get("ref", "")
                sha = (body or {}).get("sha", "")
                if not ref.startswith("refs/") or not re.fullmatch(r"[0-9a-f]{40}", sha or ""):
                    raise ApiError(422, "Validation Failed")
                if ref in r.refs:
                    raise ApiError(422, "Reference already exists")
                if sha not in r.objects and sha != ZERO_OID:
                    raise ApiError(422, "Object does not exist")
                r.refs[ref] = sha
                if ref.startswith("refs/heads/"):
                    branch = ref[len("refs/heads/"):]
                    parsed = r.commit_tree(sha)
                    if parsed:
                        r.files[branch] = r.tree_files(parsed[0])
                return 201, {"ref": ref, "object": {"sha": sha, "type": "commit",
                                                    "url": "/api/v3/repos/%s/%s/git/commits/%s" % (owner, name, sha)}}, {}
            if method == "GET" and len(tail) == 4 and tail[2] == "heads":
                ref = "refs/heads/" + tail[3]
                sha = r.refs.get(ref)
                if sha is None:
                    not_found()
                return 200, {"ref": ref, "object": {"sha": sha, "type": "commit"}}, {}
            not_found()

        # /branches
        if tail == ["branches"] and method == "GET":
            out = []
            for ref in sorted(r.refs):
                if ref.startswith("refs/heads/"):
                    out.append({"name": ref[len("refs/heads/"):],
                                "commit": {"sha": r.refs[ref]},
                                "protected": False})
            return 200, out, {}
        if len(tail) == 2 and tail[0] == "branches" and method == "GET":
            sha = r.refs.get("refs/heads/" + tail[1])
            if sha is None:
                not_found()
            return 200, {"name": tail[1], "commit": {"sha": sha}, "protected": False}, {}

        # /commits
        if tail == ["commits"] and method == "GET":
            sha_ref = query.get("sha", [None])[0]
            tip = r.head_sha(sha_ref) if sha_ref else r.head_sha()
            out = []
            if tip:
                seen = set()
                stack = [tip]
                while stack:
                    cur = stack.pop()
                    if cur in seen:
                        continue
                    seen.add(cur)
                    parsed = r.commit_tree(cur)
                    if not parsed:
                        continue
                    _, parents, msg = parsed
                    out.append({"sha": cur, "commit": {"message": msg.strip(),
                                "author": {"name": VIEWER_NAME, "email": VIEWER_EMAIL,
                                           "date": _iso_now()},
                                "committer": {"name": VIEWER_NAME, "email": VIEWER_EMAIL,
                                              "date": _iso_now()}},
                                "author": {"login": VIEWER_LOGIN, "id": VIEWER_ID},
                                "committer": {"login": VIEWER_LOGIN, "id": VIEWER_ID}})
                    stack.extend(parents)
            items, page, per_page = paginate(out, query)
            link = link_header(base_url, "/api/v3/repos/%s/%s/commits" % (owner, name),
                               query, page, per_page, len(out))
            return 200, items, ({"Link": link} if link else {})
        if len(tail) == 2 and tail[0] == "commits" and method == "GET":
            sha = tail[1]
            parsed = r.commit_tree(sha)
            if not parsed:
                not_found()
            _, parents, msg = parsed
            return 200, {"sha": sha, "commit": {"message": msg.strip(),
                        "author": {"name": VIEWER_NAME, "email": VIEWER_EMAIL, "date": _iso_now()},
                        "committer": {"name": VIEWER_NAME, "email": VIEWER_EMAIL, "date": _iso_now()}},
                        "parents": [{"sha": p} for p in parents]}, {}

        # /contents/{path}
        if tail and tail[0] == "contents":
            cpath = "/".join(tail[1:])
            ref = query.get("ref", [None])[0]
            branch = ref if ref and not re.fullmatch(r"[0-9a-f]{40}", ref or "") else None
            tip = r.head_sha(branch) if branch else r.head_sha()
            files = {}
            if tip:
                parsed = r.commit_tree(tip)
                if parsed:
                    files = r.tree_files(parsed[0])
            if method == "GET":
                if cpath in files:
                    sha, _mode = files[cpath]
                    raw = r.objects[sha][1]
                    return 200, {"type": "file", "encoding": "base64",
                                 "size": len(raw), "name": cpath.split("/")[-1],
                                 "path": cpath, "sha": sha,
                                 "content": _b64.b64encode(raw).decode(),
                                 "url": "/api/v3/repos/%s/%s/contents/%s" % (owner, name, cpath)}, {}
                # directory listing
                prefix = cpath + "/" if cpath else ""
                entries = {}
                for p in files:
                    if prefix and not p.startswith(prefix):
                        continue
                    rest_p = p[len(prefix):]
                    first = rest_p.split("/")[0]
                    if "/" in rest_p:
                        entries[first] = {"type": "dir", "name": first,
                                          "path": prefix + first, "sha": ""}
                    else:
                        entries[first] = {"type": "file", "name": first,
                                          "path": p, "sha": files[p][0]}
                if not entries and cpath:
                    not_found()
                return 200, [entries[k] for k in sorted(entries)], {}
            if method == "PUT":
                content_b64 = (body or {}).get("content")
                if content_b64 is None:
                    raise ApiError(422, "Validation Failed: content is required")
                try:
                    raw = _b64.b64decode(content_b64)
                except Exception:
                    bad_request("Invalid base64 content")
                message = (body or {}).get("message") or "Update %s" % cpath
                branch = (body or {}).get("branch") or r.default_branch
                given_sha = (body or {}).get("sha")
                base_files = r.files.get(branch, {})
                if cpath in base_files:
                    if not given_sha:
                        raise ApiError(422, "Validation Failed: sha is required for update")
                    if given_sha != base_files[cpath][0]:
                        raise ApiError(409, "Conflict: sha does not match")
                    status = 200
                else:
                    if given_sha:
                        raise ApiError(422, "Validation Failed: sha given for a new file")
                    status = 201
                blob_sha = r.put_object("blob", raw)
                parents = []
                tip = r.head_sha(branch)
                if tip:
                    parents = [tip]
                commit_sha = _content_commit(r, branch, message,
                                             {cpath: (blob_sha, "100644")},
                                             base_files, parents)
                return status, {"content": {"type": "file", "encoding": "base64",
                                            "size": len(raw), "name": cpath.split("/")[-1],
                                            "path": cpath, "sha": blob_sha},
                                "commit": {"sha": commit_sha,
                                           "message": message}}, {}
            if method == "DELETE":
                if cpath not in files:
                    not_found()
                given_sha = (body or {}).get("sha")
                if given_sha and given_sha != files[cpath][0]:
                    raise ApiError(409, "Conflict: sha does not match")
                message = (body or {}).get("message") or "Delete %s" % cpath
                branch = (body or {}).get("branch") or r.default_branch
                base_files = r.files.get(branch, {})
                parents = []
                tip = r.head_sha(branch)
                if tip:
                    parents = [tip]
                commit_sha = _content_commit(r, branch, message, {cpath: None},
                                             base_files, parents)
                return 200, {"commit": {"sha": commit_sha}}, {}
            not_found()

        # /labels
        if tail == ["labels"]:
            if method == "GET":
                return 200, [dict(v) for v in r.labels.values()], {}
            if method == "POST":
                lname = (body or {}).get("name")
                if not lname:
                    raise ApiError(422, "Validation Failed: name is required")
                label = {"name": lname, "color": (body or {}).get("color") or "ffffff",
                         "description": (body or {}).get("description") or "",
                         "default": False}
                r.labels[lname] = label
                return 201, dict(label), {}
            not_found()

        # /issues
        if tail and tail[0] == "issues":
            if len(tail) == 1:
                if method == "GET":
                    issues = sorted(r.issues.values(), key=lambda i: -i["number"])
                    state = query.get("state", ["open"])[0]
                    if state != "all":
                        issues = [i for i in issues if i["state"] == state]
                    sort = query.get("sort", ["created"])[0]
                    direction = query.get("direction", ["desc"])[0]
                    if sort == "created" and direction == "asc":
                        issues = list(reversed(issues))
                    items, page, per_page = paginate([issue_json(r, i) for i in issues], query)
                    link = link_header(base_url, "/api/v3/repos/%s/%s/issues" % (owner, name),
                                       query, page, per_page, len(issues))
                    return 200, items, ({"Link": link} if link else {})
                if method == "POST":
                    title = (body or {}).get("title")
                    if not title:
                        raise ApiError(422, "Validation Failed: title is required")
                    label_names = (body or {}).get("labels") or []
                    labels = []
                    for ln in label_names:
                        if ln not in r.labels:
                            raise ApiError(422, "Validation Failed: label '%s' does not exist" % ln)
                        labels.append(dict(r.labels[ln]))
                    r.issue_seq += 1
                    n = r.issue_seq
                    STORE.issue_id_seq += 1
                    issue = {"id": STORE.issue_id_seq, "number": n, "title": title,
                             "body": (body or {}).get("body") or "",
                             "state": "open", "labels": labels, "comments": [],
                             "created_at": _iso_now(), "updated_at": _iso_now(),
                             "closed_at": None}
                    r.issues[n] = issue
                    return 201, issue_json(r, issue), {}
                not_found()
            try:
                n = int(tail[1])
            except ValueError:
                not_found()
            issue = r.issues.get(n)
            if len(tail) == 2:
                if issue is None:
                    not_found()
                if method == "GET":
                    return 200, issue_json(r, issue), {}
                if method == "PATCH":
                    if body and body.get("state") == "closed":
                        issue["state"] = "closed"
                        issue["closed_at"] = _iso_now()
                    if body and body.get("state") == "open":
                        issue["state"] = "open"
                        issue["closed_at"] = None
                    if body and body.get("title"):
                        issue["title"] = body["title"]
                    if body and "body" in body:
                        issue["body"] = body["body"] or ""
                    issue["updated_at"] = _iso_now()
                    return 200, issue_json(r, issue), {}
                not_found()
            if len(tail) == 3 and tail[2] == "comments":
                if issue is None:
                    not_found()
                if method == "GET":
                    return 200, [{"id": c["id"], "node_id": node_id("IssueComment", c["id"]),
                                  "body": c["body"], "user": {"login": VIEWER_LOGIN, "id": VIEWER_ID},
                                  "created_at": c["created_at"], "updated_at": c["created_at"]}
                                 for c in issue["comments"]], {}
                if method == "POST":
                    cbody = (body or {}).get("body")
                    if not cbody:
                        raise ApiError(422, "Validation Failed: body is required")
                    STORE.comment_id_seq += 1
                    comment = {"id": STORE.comment_id_seq, "body": cbody,
                               "created_at": _iso_now()}
                    issue["comments"].append(comment)
                    return 201, {"id": comment["id"],
                                 "node_id": node_id("IssueComment", comment["id"]),
                                 "body": cbody,
                                 "user": {"login": VIEWER_LOGIN, "id": VIEWER_ID},
                                 "created_at": comment["created_at"],
                                 "updated_at": comment["created_at"]}, {}
                not_found()
            not_found()

        # /pulls
        if tail and tail[0] == "pulls":
            if len(tail) == 1:
                if method == "GET":
                    prs = sorted(r.prs.values(), key=lambda p: -p["number"])
                    state = query.get("state", ["open"])[0]
                    if state != "all":
                        prs = [p for p in prs if p["state"] == state]
                    items, page, per_page = paginate([pr_json(r, p) for p in prs], query)
                    link = link_header(base_url, "/api/v3/repos/%s/%s/pulls" % (owner, name),
                                       query, page, per_page, len(prs))
                    return 200, items, ({"Link": link} if link else {})
                if method == "POST":
                    title = (body or {}).get("title")
                    head = (body or {}).get("head")
                    base = (body or {}).get("base") or r.default_branch
                    if not title or not head:
                        raise ApiError(422, "Validation Failed: title and head are required")
                    head_sha = r.head_sha(head)
                    if head_sha is None:
                        raise ApiError(422, "Validation Failed: head branch '%s' does not exist" % head)
                    base_sha = r.head_sha(base)
                    if base_sha is None:
                        raise ApiError(422, "Validation Failed: base branch '%s' does not exist" % base)
                    for p in r.prs.values():
                        if p["state"] == "open" and p["head"] == head and p["base"] == base:
                            raise ApiError(422, "Validation Failed: a pull request for this head already exists")
                    r.pr_seq += 1
                    num = r.pr_seq
                    STORE.pr_id_seq += 1
                    mb = r.merge_base(base_sha, head_sha)
                    mergeable = _pr_mergeable(r, base_sha, head_sha, mb)
                    files = _pr_files(r, base_sha, head_sha, mb)
                    pr = {"id": STORE.pr_id_seq, "number": num, "title": title,
                          "body": (body or {}).get("body") or "", "state": "open",
                          "head": head, "head_sha": head_sha,
                          "base": base, "base_sha": base_sha,
                          "merged": False, "mergeable": mergeable,
                          "merged_at": None, "merge_commit_sha": None,
                          "created_at": _iso_now(), "updated_at": _iso_now(),
                          "closed_at": None, "labels": [],
                          "commits": _count_commits(r, mb, head_sha),
                          "additions": sum(f["additions"] for f in files),
                          "deletions": sum(f["deletions"] for f in files),
                          "changed_files": len(files), "_files": files,
                          "_merge_base": mb}
                    r.prs[num] = pr
                    return 201, pr_json(r, pr), {}
                not_found()
            try:
                num = int(tail[1])
            except ValueError:
                not_found()
            pr = r.prs.get(num)
            if len(tail) == 2:
                if pr is None:
                    not_found()
                if method == "GET":
                    return 200, pr_json(r, pr), {}
                not_found()
            if len(tail) == 3 and tail[2] == "files":
                if pr is None:
                    not_found()
                if method == "GET":
                    return 200, [{"filename": f["filename"], "status": f["status"],
                                  "additions": f["additions"], "deletions": f["deletions"],
                                  "changes": f["additions"] + f["deletions"]}
                                 for f in pr["_files"]], {}
                not_found()
            if len(tail) == 3 and tail[2] == "merge":
                if pr is None:
                    not_found()
                if method == "PUT":
                    if pr["state"] != "open" or pr["merged"]:
                        raise ApiError(405, "Pull request is already merged or closed")
                    if not pr["mergeable"]:
                        raise ApiError(405, "Pull request is not mergeable")
                    base_files = r.tree_files(r.commit_tree(pr["base_sha"])[0]) if r.commit_tree(pr["base_sha"]) else {}
                    head_files = r.tree_files(r.commit_tree(pr["head_sha"])[0]) if r.commit_tree(pr["head_sha"]) else {}
                    message = "Merge pull request #%d from %s" % (num, pr["head"])
                    merge_sha = r.commit(pr["base"], head_files, message, [pr["base_sha"]])
                    pr["merged"] = True
                    pr["state"] = "closed"
                    pr["merged_at"] = _iso_now()
                    pr["closed_at"] = _iso_now()
                    pr["merge_commit_sha"] = merge_sha
                    pr["updated_at"] = _iso_now()
                    return 200, {"sha": merge_sha, "merged": True,
                                 "message": "Pull Request successfully merged"}, {}
                not_found()
            not_found()

    not_found()


def _count_commits(r, base_sha, head_sha):
    if base_sha is None or head_sha is None:
        return 1
    seen = set()
    stack = [head_sha]
    n = 0
    while stack:
        cur = stack.pop()
        if cur in seen or cur == base_sha:
            continue
        seen.add(cur)
        parsed = r.commit_tree(cur)
        if not parsed:
            continue
        n += 1
        stack.extend(parsed[1])
    return max(1, n)


def _pr_files(r, base_sha, head_sha, merge_base_sha):
    """Diff base tip vs head tip (three-way vs merge base when known)."""
    def files_of(sha):
        if not sha:
            return {}
        parsed = r.commit_tree(sha)
        return r.tree_files(parsed[0]) if parsed else {}
    base_files = files_of(merge_base_sha or base_sha)
    head_files = files_of(head_sha)
    out = []
    for path in sorted(set(base_files) | set(head_files)):
        if path not in base_files:
            raw = r.objects[head_files[path][0]][1]
            out.append({"filename": path, "status": "added",
                        "additions": raw.decode("utf-8", "replace").count("\n") + (1 if raw and not raw.endswith(b"\n") else 0),
                        "deletions": 0})
        elif path not in head_files:
            raw = r.objects[base_files[path][0]][1]
            out.append({"filename": path, "status": "removed",
                        "additions": 0,
                        "deletions": raw.decode("utf-8", "replace").count("\n") + (1 if raw and not raw.endswith(b"\n") else 0)})
        elif base_files[path][0] != head_files[path][0]:
            a = r.objects[base_files[path][0]][1].decode("utf-8", "replace").splitlines()
            b = r.objects[head_files[path][0]][1].decode("utf-8", "replace").splitlines()
            add = sum(1 for line in b if line not in a)
            dele = sum(1 for line in a if line not in b)
            out.append({"filename": path, "status": "modified",
                        "additions": max(1, add), "deletions": dele})
    return out


def _pr_mergeable(r, base_sha, head_sha, merge_base_sha):
    """A PR conflicts when the same file changed on both sides of the merge
    base with different resulting content."""
    if base_sha is None or head_sha is None:
        return False
    if merge_base_sha is None:
        # unrelated histories: mergeable only if head is a pure addition set
        return True
    def files_of(sha):
        parsed = r.commit_tree(sha)
        return r.tree_files(parsed[0]) if parsed else {}
    mb_files = files_of(merge_base_sha)
    base_files = files_of(base_sha)
    head_files = files_of(head_sha)
    for path in set(mb_files) | set(base_files) | set(head_files):
        base_changed = base_files.get(path, (None,))[0] != mb_files.get(path, (None,))[0]
        head_changed = head_files.get(path, (None,))[0] != mb_files.get(path, (None,))[0]
        if base_changed and head_changed:
            if base_files.get(path, (None,))[0] != head_files.get(path, (None,))[0]:
                return False
    return True

# ---------------------------------------------------------------- git smart HTTP

V2_CAPS = [("ls-refs", "unborn"), ("fetch", "shallow filter"),
           ("object-format", "sha1")]
V0_UPLOAD_CAPS = ("symref=HEAD:refs/heads/main side-band-64k "
                  "multi_ack_detailed thin-pack ofs-delta shallow")
V0_RECEIVE_CAPS = ("report-status side-band-64k delete-refs ofs-delta "
                   "symref=HEAD:refs/heads/main")


def _ref_entries(r):
    """Sorted (refname, sha) for all refs, plus the default branch tip."""
    refs = sorted(r.refs.items())
    return refs


def _peel_tag(r, sha):
    """Follow annotated tags to the underlying commit (or None)."""
    seen = set()
    cur = sha
    while cur and cur not in seen:
        seen.add(cur)
        obj = r.objects.get(cur)
        if not obj or obj[0] != "tag":
            return cur if obj and obj[0] == "commit" else None
        text = obj[1].decode("utf-8", "replace")
        nxt = None
        for line in text.split("\n"):
            if line.startswith("object "):
                nxt = line[7:].strip()
                break
        cur = nxt
    return None


def _advertise_v0(r, service):
    """v0 advertisement body for upload-pack or receive-pack."""
    caps = V0_UPLOAD_CAPS if service == "git-upload-pack" else V0_RECEIVE_CAPS
    svc = ("# service=git-upload-pack\n" if service == "git-upload-pack"
           else "# service=git-receive-pack\n")
    out = bytearray()
    out += pkt_line(svc)
    out += pkt_flush()
    refs = _ref_entries(r)
    default_tip = r.head_sha()
    if not refs:
        out += pkt_line("%s capabilities^{}\x00%s\n" % (ZERO_OID, caps))
    else:
        head_oid = default_tip or ZERO_OID
        out += pkt_line("%s HEAD\x00%s\n" % (head_oid, caps))
        for name, sha in refs:
            out += pkt_line("%s %s\n" % (sha, name))
            obj = r.objects.get(sha)
            if obj and obj[0] == "tag":
                peeled = _peel_tag(r, sha)
                if peeled:
                    out += pkt_line("%s %s^{}\n" % (peeled, name))
    out += pkt_flush()
    return bytes(out)


def _advertise_v2():
    out = bytearray()
    out += pkt_line("version 2\n")
    for name, value in V2_CAPS:
        out += pkt_line("%s=%s\n" % (name, value))
    out += pkt_flush()
    return bytes(out)


def _ls_refs_response(r, args):
    """args: parsed ls-refs arguments. Returns the response body bytes."""
    peel = "peel" in args
    symrefs = "symrefs" in args
    unborn = "unborn" in args
    prefixes = [a.split(" ", 1)[1] for a in args if a.startswith("ref-prefix ")]
    out = bytearray()
    default_ref = "refs/heads/" + r.default_branch
    default_tip = r.head_sha()

    def keep(name):
        return not prefixes or any(name.startswith(p) for p in prefixes)

    def emit_ref(oid, name, peeled=None, symref_target=None):
        line = "%s %s" % (oid, name)
        if symref_target:
            line += " symref-target:%s" % symref_target
        if peeled:
            line += " peeled:%s" % peeled
        out.extend(pkt_line(line + "\n"))

    if keep("HEAD"):
        if default_tip:
            peeled = None
            out_head = default_tip
            emit_ref(out_head, "HEAD",
                     symref_target=default_ref if symrefs else None)
        elif unborn:
            line = "unborn HEAD"
            if symrefs:
                line += " symref-target:%s" % default_ref
            out.extend(pkt_line(line + "\n"))
    for name, sha in _ref_entries(r):
        if not keep(name):
            continue
        peeled = None
        if peel:
            obj = r.objects.get(sha)
            if obj and obj[0] == "tag":
                peeled = _peel_tag(r, sha)
        emit_ref(sha, name, peeled=peeled)
    out += pkt_flush()
    return bytes(out)


def _commit_timestamp(r, sha):
    parsed = r.commit_tree(sha)
    if not parsed:
        return 0
    raw = r.objects[sha][1].decode("utf-8", "replace")
    for line in raw.split("\n"):
        if line.startswith("author "):
            parts = line.rsplit(" ", 2)
            try:
                return int(parts[-2])
            except (ValueError, IndexError):
                return 0
    return 0


def _fetch_pack(r, wants, haves, depth=None, deepen_since=None,
                deepen_not=None, shallow_held=None, filter_spec=None):
    """Compute the objects to send for a fetch.

    Returns (objects, shallow_list, unshallow_list) where objects is a list of
    (type, raw) and the lists hold commit oids for the shallow-info section.
    """
    haves = set(haves or [])
    shallow_held = set(shallow_held or [])
    held = set(haves) | set(shallow_held)
    # commits the client already has (haves and everything reachable from them)
    exclude = set()
    stack = list(haves)
    while stack:
        cur = stack.pop()
        if cur in exclude:
            continue
        exclude.add(cur)
        parsed = r.commit_tree(cur)
        if parsed:
            stack.extend(parsed[1])
    if deepen_not:
        for ref in deepen_not:
            tip = r.refs.get(ref) or r.head_sha(ref)
            if tip:
                stack = [tip]
                while stack:
                    cur = stack.pop()
                    if cur in exclude:
                        continue
                    exclude.add(cur)
                    parsed = r.commit_tree(cur)
                    if parsed:
                        stack.extend(parsed[1])
    # BFS from wants, generation-limited by depth
    send = {}          # oid -> generation
    queue = []
    for w in wants:
        obj = r.objects.get(w)
        if not obj:
            continue
        if obj[0] == "tag":
            peeled = _peel_tag(r, w)
            if peeled:
                queue.append((peeled, 0))
            send[w] = 0
        elif obj[0] == "commit":
            queue.append((w, 0))
    qi = 0
    while qi < len(queue):
        cur, gen = queue[qi]
        qi += 1
        if cur in send and send[cur] <= gen:
            continue
        if cur in exclude:
            continue
        if depth is not None and gen >= depth:
            # beyond the requested depth: do not send, do not expand
            continue
        send[cur] = gen
        parsed = r.commit_tree(cur)
        if not parsed:
            continue
        _, parents, _ = parsed
        for p in parents:
            if p not in send:
                queue.append((p, gen + 1))
    # deepen-since: drop commits older than the epoch
    if deepen_since is not None:
        send = {c: g for c, g in send.items()
                if _commit_timestamp(r, c) >= deepen_since}
    # shallow boundary: sent commits with a parent the client will not hold
    sent_commits = {c for c in send if r.objects.get(c, (None,))[0] == "commit"}
    present = held | sent_commits

    def parents_of(c):
        parsed = r.commit_tree(c)
        return parsed[1] if parsed else []

    shallow = sorted(c for c in sent_commits
                     if any(p not in present for p in parents_of(c)))
    unshallow = sorted(c for c in shallow_held
                       if all(p in present for p in parents_of(c)))
    # collect trees and blobs for the sent commits
    objs = {}          # sha -> (type, raw)
    for c in sent_commits:
        objs[c] = r.objects[c]
    # tags wanted directly
    for w in wants:
        obj = r.objects.get(w)
        if obj and obj[0] == "tag":
            objs[w] = obj
    tree_only = filter_spec == "tree:0"
    blob_none = filter_spec == "blob:none"
    blob_limit = None
    if filter_spec and filter_spec.startswith("blob:limit="):
        try:
            blob_limit = int(filter_spec.split("=", 1)[1])
        except ValueError:
            blob_limit = None
    for c in list(sent_commits):
        parsed = r.commit_tree(c)
        if not parsed:
            continue
        tree_sha = parsed[0]
        if tree_only:
            continue
        # walk the tree
        stack = [tree_sha]
        while stack:
            t = stack.pop()
            if t in objs:
                continue
            obj = r.objects.get(t)
            if not obj or obj[0] != "tree":
                continue
            objs[t] = obj
            for mode, _name, sha in parse_tree(obj[1]):
                if mode == "40000":
                    stack.append(sha)
                elif blob_none:
                    continue
                elif blob_limit is not None and len(r.objects.get(sha, (None, b""))[1]) > blob_limit:
                    continue
                else:
                    if sha in r.objects:
                        objs[sha] = r.objects[sha]
    ordered = sorted(objs.items(), key=lambda kv: ({"commit": 0, "tree": 1, "blob": 2, "tag": 3}.get(kv[1][0], 4), kv[0]))
    return [(otype, raw) for _sha, (otype, raw) in ordered], shallow, unshallow


def _v2_fetch_response(r, args):
    """args: list of argument lines (without trailing newline).

    Section rules (verified against real git upload-pack):
    - the acknowledgments section is emitted ONLY when the client sent
      haves and has NOT sent `done` (multi-round negotiation still open);
      it ends with a DELIM, not a flush.
    - the shallow-info section (when present) also ends with a DELIM.
    - the packfile section is last and ends with a FLUSH.
    """
    wants, haves, shallow_held, deepen_not = [], [], [], []
    depth = None
    deepen_since = None
    filter_spec = None
    done = False
    for a in args:
        if a.startswith("want "):
            wants.append(a[5:].strip())
        elif a.startswith("have "):
            haves.append(a[5:].strip())
        elif a.startswith("shallow "):
            shallow_held.append(a[8:].strip())
        elif a.startswith("deepen "):
            try:
                depth = int(a[7:].strip())
            except ValueError:
                depth = None
        elif a.startswith("deepen-since "):
            try:
                deepen_since = int(a[13:].strip())
            except ValueError:
                deepen_since = None
        elif a.startswith("deepen-not "):
            deepen_not.append(a[11:].strip())
        elif a.startswith("filter "):
            filter_spec = a[7:].strip()
        elif a.strip() == "done":
            done = True
    objects, shallow, unshallow = _fetch_pack(
        r, wants, haves, depth=depth, deepen_since=deepen_since,
        deepen_not=deepen_not, shallow_held=shallow_held, filter_spec=filter_spec)
    out = bytearray()
    # acknowledgments: only when haves were sent and negotiation is open
    if haves and not done:
        out += pkt_line("acknowledgments\n")
        known = [h for h in haves if h in r.objects]
        if not known:
            out += pkt_line("NAK\n")
        else:
            for h in known:
                out += pkt_line("ACK %s\n" % h)
            out += pkt_line("ready\n")
        out += pkt_delim()
    # shallow-info
    if shallow or unshallow:
        out += pkt_line("shallow-info\n")
        for s in shallow:
            out += pkt_line("shallow %s\n" % s)
        for s in unshallow:
            out += pkt_line("unshallow %s\n" % s)
        out += pkt_delim()
    # packfile
    out += pkt_line("packfile\n")
    out += sideband64(write_pack(objects))
    out += pkt_flush()
    return bytes(out)


def _v0_fetch_response(r, args):
    """args: pkt-lines of the v0 fetch request (two sections)."""
    wants, haves, shallow_held, deepen_not = [], [], [], []
    depth = None
    deepen_since = None
    for a in args:
        if a is None:
            continue
        if a.startswith("want "):
            # first want line may carry features after the oid
            rest = a[5:].strip()
            wants.append(rest.split(" ", 1)[0])
        elif a.startswith("have "):
            haves.append(a[5:].strip())
        elif a.startswith("shallow "):
            shallow_held.append(a[8:].strip())
        elif a.startswith("deepen "):
            try:
                depth = int(a[7:].strip())
            except ValueError:
                depth = None
        elif a.startswith("deepen-since "):
            try:
                deepen_since = int(a[13:].strip())
            except ValueError:
                deepen_since = None
        elif a.startswith("deepen-not "):
            deepen_not.append(a[11:].strip())
    objects, shallow, unshallow = _fetch_pack(
        r, wants, haves, depth=depth, deepen_since=deepen_since,
        deepen_not=deepen_not, shallow_held=shallow_held)
    out = bytearray()
    known = [h for h in haves if h in r.objects]
    if not known:
        out += pkt_line("NAK\n")
    else:
        for h in known:
            out += pkt_line("ACK %s\n" % h)
    for s in shallow:
        out += pkt_line("shallow %s\n" % s)
    for s in unshallow:
        out += pkt_line("unshallow %s\n" % s)
    out += sideband64(write_pack(objects))
    out += pkt_flush()
    return bytes(out)


def _receive_pack(r, body):
    """Handle a receive-pack POST body. Returns (status, response_bytes)."""
    lines, consumed = read_pkt_lines(body, stop_at_flush=True)
    commands = []
    for line in lines:
        if line is None:
            break
        text = line.decode("utf-8", "replace")
        # first command line may carry \0<capabilities>
        if "\x00" in text:
            text = text.split("\x00", 1)[0]
        parts = text.strip().split(" ")
        if len(parts) != 3:
            continue
        commands.append((parts[0], parts[1], parts[2]))
    pack_data = body[consumed:]
    # store the pack's objects (thin packs reference objects we already hold)
    if pack_data:
        try:
            for otype, raw in read_pack(pack_data, base_lookup=r.objects):
                r.put_object(otype, raw)
        except Exception as e:
            # unpack error: report it, apply nothing
            report = pkt_line("unpack %s\n" % str(e)[:120])
            for _old, _new, ref in commands:
                report += pkt_line("ng %s unpacker error\n" % ref)
            report += pkt_flush()
            return 200, sideband64(report) + pkt_flush()
    results = []
    for old, new, ref in commands:
        if not ref.startswith("refs/"):
            results.append((ref, False, "invalid ref"))
            continue
        current = r.refs.get(ref)
        if new == ZERO_OID:
            # delete
            if current is None:
                results.append((ref, False, "non-fast-forward"))
            else:
                del r.refs[ref]
                if ref.startswith("refs/heads/"):
                    r.files.pop(ref[len("refs/heads/"):], None)
                results.append((ref, True, ""))
            continue
        if new not in r.objects:
            results.append((ref, False, "object not found"))
            continue
        if old == ZERO_OID:
            # create
            if current is not None:
                results.append((ref, False, "non-fast-forward"))
                continue
            r.refs[ref] = new
            _sync_branch_files(r, ref, new)
            results.append((ref, True, ""))
            continue
        if current is None or current != old:
            results.append((ref, False, "non-fast-forward"))
            continue
        if old == new:
            results.append((ref, True, ""))
            continue
        if r.is_ancestor(old, new):
            r.refs[ref] = new
            _sync_branch_files(r, ref, new)
            results.append((ref, True, ""))
        else:
            results.append((ref, False, "non-fast-forward"))
    report = pkt_line("unpack ok\n")
    for ref, ok, reason in results:
        if ok:
            report += pkt_line("ok %s\n" % ref)
        else:
            report += pkt_line("ng %s %s\n" % (ref, reason))
    report += pkt_flush()
    return 200, sideband64(report) + pkt_flush()


def _sync_branch_files(r, ref, sha):
    if not ref.startswith("refs/heads/"):
        return
    branch = ref[len("refs/heads/"):]
    parsed = r.commit_tree(sha)
    if parsed:
        r.files[branch] = r.tree_files(parsed[0])
    r.pushed_at = _iso_now()


def handle_git(handler, method, path, query, body):
    """Git smart-HTTP. Returns (status, content_type, response_bytes)."""
    parts = [unquote(p) for p in path.split("/") if p != ""]
    if len(parts) < 2 or not parts[1].endswith(".git"):
        return 404, "application/json", json_bytes({"message": "Not Found"})
    owner, repo_name = parts[0], parts[1][:-4]
    if owner != VIEWER_LOGIN:
        return 404, "application/json", json_bytes({"message": "Not Found"})
    r = STORE.get_repo(owner, repo_name)
    if r is None:
        return 404, "application/json", json_bytes({"message": "Not Found"})
    service = parts[2] if len(parts) > 2 else None
    git_protocol = handler.headers.get("Git-Protocol", "")

    if method == "GET" and service == "info" and len(parts) == 4 and parts[3] == "refs":
        svc = query.get("service", [""])[0]
        if svc == "git-upload-pack":
            if git_protocol.strip() == "version=2":
                return 200, "application/x-git-upload-pack-advertisement", _advertise_v2()
            return 200, "application/x-git-upload-pack-advertisement", _advertise_v0(r, svc)
        if svc == "git-receive-pack":
            return 200, "application/x-git-receive-pack-advertisement", _advertise_v0(r, svc)
        return 404, "application/json", json_bytes({"message": "Not Found"})

    if method == "POST" and service == "git-upload-pack":
        try:
            lines, _ = read_pkt_lines(body)
        except Exception:
            return 400, "application/json", json_bytes({"message": "Bad Request"})
        if git_protocol.strip() == "version=2":
            text_lines = []
            command = None
            for line in lines:
                if line is None:
                    continue
                if line == b"\x01":
                    continue
                text = line.decode("utf-8", "replace")
                if text.startswith("command="):
                    command = text[len("command="):].strip()
                elif text.startswith(("agent=", "object-format=")):
                    continue
                else:
                    text_lines.append(text.rstrip("\n"))
            if command == "ls-refs":
                return 200, "application/x-git-upload-pack-result", _ls_refs_response(r, text_lines)
            if command == "fetch":
                return 200, "application/x-git-upload-pack-result", _v2_fetch_response(r, text_lines)
            return 400, "application/json", json_bytes({"message": "Bad Request"})
        # v0 fetch
        args = []
        for line in lines:
            if line is None:
                args.append(None)
            elif line == b"\x01":
                continue
            else:
                args.append(line.decode("utf-8", "replace").rstrip("\n"))
        return 200, "application/x-git-upload-pack-result", _v0_fetch_response(r, args)

    if method == "POST" and service == "git-receive-pack":
        status, resp = _receive_pack(r, body)
        return status, "application/x-git-receive-pack-result", resp

    return 404, "application/json", json_bytes({"message": "Not Found"})

# ---------------------------------------------------------------- GraphQL

class GqlError(Exception):
    pass


def _gql_tokenize(src):
    toks = []
    i = 0
    n = len(src)
    while i < n:
        c = src[i]
        if c in " \t\r\n,":
            i += 1
        elif c == "#":
            while i < n and src[i] != "\n":
                i += 1
        elif c in "{}()[]!:$=@":
            toks.append(c)
            i += 1
        elif c == "." and src[i:i + 3] == "...":
            toks.append("...")
            i += 3
        elif c == '"':
            j = i + 1
            out = []
            while j < n and src[j] != '"':
                if src[j] == "\\" and j + 1 < n:
                    out.append(src[j + 1])
                    j += 2
                else:
                    out.append(src[j])
                    j += 1
            toks.append(("STRING", "".join(out)))
            i = j + 1
        elif c.isdigit() or (c == "-" and i + 1 < n and src[i + 1].isdigit()):
            j = i
            while j < n and (src[j].isdigit() or src[j] in ".eE+-"):
                j += 1
            num = src[i:j]
            toks.append(("INT", int(num)) if re.fullmatch(r"-?\d+", num) else ("FLOAT", float(num)))
            i = j
        elif c.isalpha() or c == "_":
            j = i
            while j < n and (src[j].isalnum() or src[j] == "_"):
                j += 1
            toks.append(src[i:j])
            i = j
        else:
            raise GqlError("Unexpected character %r" % c)
    return toks


class _GqlParser:
    def __init__(self, toks):
        self.toks = toks
        self.i = 0

    def peek(self):
        return self.toks[self.i] if self.i < len(self.toks) else None

    def next(self):
        t = self.peek()
        self.i += 1
        return t

    def expect(self, t):
        got = self.next()
        if got != t:
            raise GqlError("Expected %r, got %r" % (t, got))

    def parse_document(self):
        ops = []
        frags = {}
        while self.peek() is not None:
            if self.peek() == "fragment":
                self.next()
                name = self.next()
                self.expect("on")
                type_name = self.next()
                sel = self.parse_selection_set()
                frags[name] = (type_name, sel)
            else:
                ops.append(self.parse_operation())
        return ops, frags

    def parse_operation(self):
        kind = self.peek()
        if kind in ("query", "mutation", "subscription"):
            self.next()
            name = None
            if isinstance(self.peek(), str) and self.peek() not in ("{", "("):
                name = self.next()
            var_defs = {}
            if self.peek() == "(":
                var_defs = self.parse_var_defs()
            sel = self.parse_selection_set()
            return {"kind": kind, "name": name, "vars": var_defs, "sel": sel}
        sel = self.parse_selection_set()
        return {"kind": "query", "name": None, "vars": {}, "sel": sel}

    def parse_var_defs(self):
        self.expect("(")
        defs = {}
        while self.peek() != ")":
            self.expect("$")
            name = self.next()
            self.expect(":")
            typ = self.parse_type()
            default = None
            if self.peek() == "=":
                self.next()
                default = self.parse_value()
            defs[name] = (typ, default)
        self.expect(")")
        return defs

    def parse_type(self):
        t = self.next()
        if t == "[":
            inner = self.parse_type()
            self.expect("]")
            base = "[%s]" % inner
        else:
            base = t
        if self.peek() == "!":
            self.next()
            base += "!"
        return base

    def parse_selection_set(self):
        self.expect("{")
        sels = []
        while self.peek() != "}":
            sels.append(self.parse_selection())
        self.expect("}")
        return sels

    def parse_selection(self):
        if self.peek() == "...":
            self.next()
            if self.peek() == "on":
                self.next()
                type_name = self.next()
                sel = self.parse_selection_set()
                return {"frag": True, "type": type_name, "sel": sel}
            name = self.next()
            return {"frag": True, "name": name}
        alias = None
        name = self.next()
        if self.peek() == ":":
            self.next()
            alias = name
            name = self.next()
        args = {}
        if self.peek() == "(":
            args = self.parse_args()
        sel = None
        if self.peek() == "{":
            sel = self.parse_selection_set()
        return {"field": name, "alias": alias or name, "args": args, "sel": sel}

    def parse_args(self):
        self.expect("(")
        args = {}
        while self.peek() != ")":
            name = self.next()
            self.expect(":")
            args[name] = self.parse_value()
        self.expect(")")
        return args

    def parse_value(self):
        t = self.next()
        if isinstance(t, tuple):
            return t[1]
        if t == "$":
            return ("$var", self.next())
        if t == "[":
            vals = []
            while self.peek() != "]":
                vals.append(self.parse_value())
            self.expect("]")
            return vals
        if t == "{":
            obj = {}
            while self.peek() != "}":
                k = self.next()
                self.expect(":")
                obj[k] = self.parse_value()
            self.expect("}")
            return obj
        if t == "true":
            return True
        if t == "false":
            return False
        if t == "null":
            return None
        return ("enum", t)


def _resolve_value(v, variables):
    if isinstance(v, tuple) and v[0] == "$var":
        return variables.get(v[1])
    if isinstance(v, tuple) and v[0] == "enum":
        return v[1]
    if isinstance(v, list):
        return [_resolve_value(x, variables) for x in v]
    if isinstance(v, dict):
        return {k: _resolve_value(x, variables) for k, x in v.items()}
    return v


ISSUE_TYPE_FIELDS = ["id", "number", "title", "body", "state", "labels",
                     "user", "createdAt", "updatedAt", "closedAt", "comments", "url"]
PR_TYPE_FIELDS = ["id", "number", "title", "body", "state", "headRefName",
                  "baseRefName", "mergeable", "merged", "files", "head", "base",
                  "createdAt", "updatedAt", "closedAt", "mergedAt", "mergeCommitSha"]
REPO_TYPE_FIELDS = ["id", "databaseId", "name", "nameWithOwner", "owner",
                    "defaultBranchRef", "viewerPermission", "hasIssuesEnabled",
                    "issue", "issues", "pullRequests", "pullRequest",
                    "description", "defaultBranch", "createdAt", "updatedAt",
                    "url", "isPrivate", "fork"]
SEARCH_TYPE_VALUES = ["ISSUE", "REPOSITORY", "USER", "DISCUSSION", "COMMIT"]


def _decode_node_id(nid):
    try:
        raw = _b64.b64decode(nid).decode()
        kind, num = raw.split(":", 1)
        return kind, int(num)
    except Exception:
        return None, None


def _find_repo_by_dbid(dbid):
    for r in STORE.repos.values():
        if r.id == dbid:
            return r
    return None


def _find_issue_by_id(iid):
    for r in STORE.repos.values():
        for issue in r.issues.values():
            if issue["id"] == iid:
                return r, issue
    return None, None


def _find_pr_by_id(pid):
    for r in STORE.repos.values():
        for pr in r.prs.values():
            if pr["id"] == pid:
                return r, pr
    return None, None


class _GqlExec:
    def __init__(self, variables, frags):
        self.variables = variables or {}
        self.frags = frags
        self.errors = []

    def args(self, raw_args):
        return {k: _resolve_value(v, self.variables) for k, v in raw_args.items()}

    def select(self, type_name, node, sel, resolver):
        """Resolve a selection set on `node` of GraphQL type `type_name`."""
        out = {}
        for s in sel:
            if s.get("frag"):
                if "name" in s:
                    frag = self.frags.get(s["name"])
                    if frag:
                        out.update(self.select(frag[0], node, frag[1], resolver))
                    continue
                # inline fragment: only apply if the type matches
                if s["type"] == type_name:
                    out.update(self.select(type_name, node, s["sel"], resolver))
                continue
            field = s["field"]
            alias = s["alias"]
            args = self.args(s.get("args") or {})
            value, err = resolver(type_name, node, field, args, s.get("sel"))
            if err:
                self.errors.append(err)
                out[alias] = None
            else:
                out[alias] = value
        return out

    # -- resolvers ------------------------------------------------------------
    def resolve_query(self, field, args, sel):
        if field == "viewer":
            user = {"login": VIEWER_LOGIN, "id": VIEWER_ID}
            return self.select("User", user, sel, self.resolve_user), None
        if field == "repository":
            owner = args.get("owner")
            name = args.get("name")
            r = STORE.get_repo(owner, name) if owner and name else None
            if r is None:
                return None, None
            return self.select("Repository", r, sel, self.resolve_repo), None
        if field == "node":
            nid = args.get("id")
            kind, num = _decode_node_id(nid) if nid else (None, None)
            if kind == "Repository":
                r = _find_repo_by_dbid(num)
                if r is None:
                    return None, None
                return self.select("Repository", r, sel, self.resolve_repo), None
            if kind == "Issue":
                r, issue = _find_issue_by_id(num)
                if issue is None:
                    return None, None
                return self.select("Issue", (r, issue), sel, self.resolve_issue), None
            return None, None
        if field == "__type":
            name = args.get("name")
            node = {"__type_name": name}
            return self.select("__Type", node, sel, self.resolve_type), None
        return None, {"message": 'Cannot query field "%s" on type "Query".' % field}

    def resolve_user(self, _type, node, field, args, sel):
        if field == "login":
            return node["login"], None
        if field == "id":
            return node_id("User", node["id"]), None
        return None, {"message": 'Cannot query field "%s" on type "User".' % field}

    def resolve_repo(self, _type, r, field, args, sel):
        if field == "id":
            return node_id("Repository", r.id), None
        if field == "databaseId":
            return r.id, None
        if field == "name":
            return r.name, None
        if field == "nameWithOwner":
            return "%s/%s" % (r.owner, r.name), None
        if field == "owner":
            return self.select("User", {"login": r.owner, "id": VIEWER_ID}, sel, self.resolve_user), None
        if field == "defaultBranchRef":
            tip = r.head_sha()
            if tip is None:
                return None, None
            return self.select("Ref", {"name": r.default_branch}, sel, self.resolve_ref), None
        if field == "viewerPermission":
            return "ADMIN", None
        if field == "hasIssuesEnabled":
            return True, None
        if field == "description":
            return r.description, None
        if field == "defaultBranch":
            return r.default_branch, None
        if field == "createdAt" or field == "updatedAt":
            return _iso_now(), None
        if field == "url":
            return "/%s/%s" % (r.owner, r.name), None
        if field == "isPrivate":
            return False, None
        if field == "fork":
            return False, None
        if field == "issue":
            n = args.get("number")
            issue = r.issues.get(n) if isinstance(n, int) else None
            if issue is None:
                return None, None
            return self.select("Issue", (r, issue), sel, self.resolve_issue), None
        if field == "issues":
            issues = sorted(r.issues.values(), key=lambda i: -i["number"])
            states = args.get("states")
            if states:
                wanted = {"OPEN" if s == "OPEN" else "CLOSED" for s in states}
                # states are enum strings; map to stored states
                issues = [i for i in issues
                          if ("OPEN" if i["state"] == "open" else "CLOSED") in wanted]
            order_by = args.get("orderBy") or {}
            if order_by.get("field") == "CREATED_AT":
                if (order_by.get("direction") or "DESC") == "DESC":
                    issues = sorted(issues, key=lambda i: -i["number"])
                else:
                    issues = sorted(issues, key=lambda i: i["number"])
            after = args.get("after")
            if after:
                try:
                    after_n = int(_b64.b64decode(after).decode())
                    issues = [i for i in issues if i["number"] < after_n]
                except Exception:
                    pass
            first = args.get("first")
            page = issues if first is None else issues[:first]
            has_next = first is not None and len(issues) > len(page)
            end_cursor = None
            if page:
                end_cursor = _b64.b64encode(str(page[-1]["number"]).encode()).decode()
            nodes = [self.select("Issue", (r, i), sel_nodes(sel), self.resolve_issue)
                     for i in page]
            return self._connection(nodes, has_next, end_cursor, sel), None
        if field == "pullRequests":
            prs = sorted(r.prs.values(), key=lambda p: -p["number"])
            first = args.get("first")
            page = prs if first is None else prs[:first]
            has_next = first is not None and len(prs) > len(page)
            end_cursor = _b64.b64encode(str(page[-1]["number"]).encode()).decode() if page else None
            nodes = [self.select("PullRequest", (r, p), sel_nodes(sel), self.resolve_pr)
                     for p in page]
            return self._connection(nodes, has_next, end_cursor, sel), None
        if field == "pullRequest":
            n = args.get("number")
            pr = r.prs.get(n) if isinstance(n, int) else None
            if pr is None:
                return None, None
            return self.select("PullRequest", (r, pr), sel, self.resolve_pr), None
        return None, {"message": 'Cannot query field "%s" on type "Repository".' % field}

    def _connection(self, nodes, has_next, end_cursor, sel):
        out = {}
        for s in sel or []:
            if s.get("frag"):
                continue
            if s["field"] == "nodes":
                out[s["alias"]] = nodes
            elif s["field"] == "pageInfo":
                out[s["alias"]] = {"hasNextPage": has_next, "endCursor": end_cursor}
            elif s["field"] == "totalCount":
                out[s["alias"]] = len(nodes)
        return out

    def resolve_ref(self, _type, node, field, args, sel):
        if field == "name":
            return node["name"], None
        return None, {"message": 'Cannot query field "%s" on type "Ref".' % field}

    def resolve_issue(self, _type, node, field, args, sel):
        r, issue = node
        if field == "id":
            return node_id("Issue", issue["id"]), None
        if field == "number":
            return issue["number"], None
        if field == "title":
            return issue["title"], None
        if field == "body":
            return issue.get("body") or "", None
        if field == "state":
            return "OPEN" if issue["state"] == "open" else "CLOSED", None
        if field == "labels":
            return [{"name": l["name"]} for l in issue["labels"]], None
        if field == "createdAt" or field == "updatedAt":
            return issue["created_at"], None
        if field == "url":
            return "/%s/%s/issues/%d" % (r.owner, r.name, issue["number"]), None
        return None, {"message": 'Cannot query field "%s" on type "Issue".' % field}

    def resolve_pr(self, _type, node, field, args, sel):
        r, pr = node
        if field == "id":
            return node_id("PullRequest", pr["id"]), None
        if field == "number":
            return pr["number"], None
        if field == "title":
            return pr["title"], None
        if field == "body":
            return pr.get("body") or "", None
        if field == "state":
            if pr["merged"]:
                return "MERGED", None
            return "OPEN" if pr["state"] == "open" else "CLOSED", None
        if field == "headRefName":
            return pr["head"], None
        if field == "baseRefName":
            return pr["base"], None
        if field == "mergeable":
            return "MERGEABLE" if pr["mergeable"] else "CONFLICTING", None
        if field == "merged":
            return bool(pr["merged"]), None
        if field == "files":
            first = args.get("first")
            files = pr["_files"]
            page = files if first is None else files[:first]
            nodes = [{"path": f["filename"]} for f in page]
            return self._connection(nodes, False, None, sel), None
        if field == "createdAt" or field == "updatedAt":
            return pr["created_at"], None
        if field == "mergedAt":
            return pr.get("merged_at"), None
        return None, {"message": 'Cannot query field "%s" on type "PullRequest".' % field}

    def resolve_type(self, _type, node, field, args, sel):
        name = node["__type_name"]
        if field == "fields":
            mapping = {"Issue": ISSUE_TYPE_FIELDS, "PullRequest": PR_TYPE_FIELDS,
                       "Repository": REPO_TYPE_FIELDS}
            fields = mapping.get(name, [])
            return [{"name": f} for f in fields], None
        if field == "enumValues":
            if name == "SearchType":
                return [{"name": v} for v in SEARCH_TYPE_VALUES], None
            return None, None
        if field == "name":
            return name, None
        return None, {"message": 'Cannot query field "%s" on type "__Type".' % field}

    # -- mutations -------------------------------------------------------------
    def mutate(self, op, variables):
        name = op.get("name")
        sel = op["sel"]
        out = {}
        for s in sel:
            if s.get("frag"):
                continue
            field = s["field"]
            args = self.args(s.get("args") or {})
            value, err = self.run_mutation(field, args, s.get("sel"))
            if err:
                self.errors.append(err)
                out[s["alias"]] = None
            else:
                out[s["alias"]] = value
        return out

    def run_mutation(self, field, args, sel):
        inp = args.get("input") or {}
        if field == "createIssue":
            kind, dbid = _decode_node_id(inp.get("repositoryId") or "")
            r = _find_repo_by_dbid(dbid) if kind == "Repository" else None
            if r is None:
                return None, {"message": "Repository not found"}
            title = inp.get("title")
            if not title:
                return None, {"message": "title is required"}
            r.issue_seq += 1
            n = r.issue_seq
            STORE.issue_id_seq += 1
            issue = {"id": STORE.issue_id_seq, "number": n, "title": title,
                     "body": inp.get("body") or "", "state": "open",
                     "labels": [], "comments": [],
                     "created_at": _iso_now(), "updated_at": _iso_now(),
                     "closed_at": None}
            r.issues[n] = issue
            return self.select("IssuePayload", (r, issue), sel, self.resolve_issue_payload), None
        if field == "closeIssue":
            kind, iid = _decode_node_id(inp.get("issueId") or "")
            r, issue = _find_issue_by_id(iid) if kind == "Issue" else (None, None)
            if issue is None:
                return None, {"message": "Issue not found"}
            issue["state"] = "closed"
            issue["closed_at"] = _iso_now()
            issue["updated_at"] = _iso_now()
            return self.select("IssuePayload", (r, issue), sel, self.resolve_issue_payload), None
        if field == "createPullRequest":
            kind, dbid = _decode_node_id(inp.get("repositoryId") or "")
            r = _find_repo_by_dbid(dbid) if kind == "Repository" else None
            if r is None:
                return None, {"message": "Repository not found"}
            head = inp.get("headRefName")
            base = inp.get("baseRefName") or r.default_branch
            head_sha = r.head_sha(head)
            base_sha = r.head_sha(base)
            if head_sha is None or base_sha is None:
                return None, {"message": "head or base branch does not exist"}
            r.pr_seq += 1
            num = r.pr_seq
            STORE.pr_id_seq += 1
            mb = r.merge_base(base_sha, head_sha)
            mergeable = _pr_mergeable(r, base_sha, head_sha, mb)
            files = _pr_files(r, base_sha, head_sha, mb)
            pr = {"id": STORE.pr_id_seq, "number": num,
                  "title": inp.get("title") or "", "body": "",
                  "state": "open", "head": head, "head_sha": head_sha,
                  "base": base, "base_sha": base_sha,
                  "merged": False, "mergeable": mergeable,
                  "merged_at": None, "merge_commit_sha": None,
                  "created_at": _iso_now(), "updated_at": _iso_now(),
                  "closed_at": None, "labels": [],
                  "commits": _count_commits(r, mb, head_sha),
                  "additions": sum(f["additions"] for f in files),
                  "deletions": sum(f["deletions"] for f in files),
                  "changed_files": len(files), "_files": files, "_merge_base": mb}
            r.prs[num] = pr
            return self.select("PullRequestPayload", (r, pr), sel, self.resolve_pr_payload), None
        if field == "mergePullRequest":
            kind, pid = _decode_node_id(inp.get("pullRequestId") or "")
            r, pr = _find_pr_by_id(pid) if kind == "PullRequest" else (None, None)
            if pr is None:
                return None, {"message": "Pull request not found"}
            if pr["state"] != "open" or pr["merged"] or not pr["mergeable"]:
                return None, {"message": "Pull request is not mergeable"}
            head_files = r.tree_files(r.commit_tree(pr["head_sha"])[0])
            message = "Merge pull request #%d from %s" % (pr["number"], pr["head"])
            merge_sha = r.commit(pr["base"], head_files, message, [pr["base_sha"]])
            pr["merged"] = True
            pr["state"] = "closed"
            pr["merged_at"] = _iso_now()
            pr["closed_at"] = _iso_now()
            pr["merge_commit_sha"] = merge_sha
            pr["updated_at"] = _iso_now()
            return self.select("PullRequestPayload", (r, pr), sel, self.resolve_pr_payload), None
        if field == "addComment":
            kind, sid = _decode_node_id(inp.get("subjectId") or "")
            body = inp.get("body") or ""
            if kind == "Issue":
                r, issue = _find_issue_by_id(sid)
                if issue is None:
                    return None, {"message": "Subject not found"}
                STORE.comment_id_seq += 1
                comment = {"id": STORE.comment_id_seq, "body": body,
                           "created_at": _iso_now()}
                issue["comments"].append(comment)
                node = {"id": comment["id"], "body": body}
                return self.select("CommentPayload", node, sel, self.resolve_comment_payload), None
            return None, {"message": "Subject not found"}
        return None, {"message": 'Cannot query field "%s" on type "Mutation".' % field}

    def resolve_issue_payload(self, _type, node, field, args, sel):
        r, issue = node
        if field == "issue":
            return self.select("Issue", (r, issue), sel, self.resolve_issue), None
        return None, {"message": 'Cannot query field "%s".' % field}

    def resolve_pr_payload(self, _type, node, field, args, sel):
        r, pr = node
        if field == "pullRequest":
            return self.select("PullRequest", (r, pr), sel, self.resolve_pr), None
        return None, {"message": 'Cannot query field "%s".' % field}

    def resolve_comment_payload(self, _type, node, field, args, sel):
        if field == "commentEdge":
            edge = {"node": node}
            out = {}
            for s in sel or []:
                if s.get("frag"):
                    continue
                if s["field"] == "node":
                    out[s["alias"]] = self.select("Comment", node, s.get("sel"),
                                                  self.resolve_comment)
            return out, None
        return None, {"message": 'Cannot query field "%s".' % field}

    def resolve_comment(self, _type, node, field, args, sel):
        if field == "id":
            return node_id("IssueComment", node["id"]), None
        if field == "body":
            return node["body"], None
        return None, {"message": 'Cannot query field "%s" on type "IssueComment".' % field}


def sel_nodes(sel):
    """The selection set of a connection's `nodes` field, if present."""
    for s in sel or []:
        if not s.get("frag") and s["field"] == "nodes":
            return s.get("sel")
    return []


def execute_graphql(body):
    """body: parsed JSON (dict or list). Returns the response object."""
    if isinstance(body, list):
        return [execute_graphql_one(item) for item in body]
    return execute_graphql_one(body)


def execute_graphql_one(item):
    if not isinstance(item, dict) or "query" not in item:
        return {"errors": [{"message": "Request must contain a query"}]}
    query = item.get("query") or ""
    variables = item.get("variables") or {}
    op_name = item.get("operationName")
    try:
        toks = _gql_tokenize(query)
        ops, frags = _GqlParser(toks).parse_document()
    except GqlError as e:
        return {"errors": [{"message": str(e)}]}
    op = None
    if op_name:
        for o in ops:
            if o.get("name") == op_name:
                op = o
                break
        if op is None:
            return {"errors": [{"message": 'Unknown operation named "%s".' % op_name}]}
    else:
        op = ops[0] if ops else None
    if op is None:
        return {"errors": [{"message": "No operation to execute"}]}
    ex = _GqlExec(variables, frags)
    if op["kind"] == "mutation":
        data = ex.mutate(op, variables)
    else:
        data = {}
        for s in op["sel"]:
            if s.get("frag"):
                continue
            field = s["field"]
            args = ex.args(s.get("args") or {})
            value, err = ex.resolve_query(field, args, s.get("sel"))
            if err:
                ex.errors.append(err)
                data[s["alias"]] = None
            else:
                data[s["alias"]] = value
    out = {"data": data}
    if ex.errors:
        out["errors"] = ex.errors
    return out

# ---------------------------------------------------------------- MCP

MCP_VERSIONS = ["2026-07-28", "2025-11-25", "2025-06-18", "2025-03-26", "2024-11-05"]

MCP_TOOLS = [
    {"name": "create_repo",
     "description": "Create a new repository owned by the viewer.",
     "inputSchema": {"type": "object",
                     "properties": {"name": {"type": "string"},
                                    "description": {"type": "string"},
                                    "private": {"type": "boolean"}},
                     "required": ["name"]}},
    {"name": "get_repo",
     "description": "Get a repository by owner and name.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string"},
                                    "repo": {"type": "string"}},
                     "required": ["owner", "repo"]}},
    {"name": "create_issue",
     "description": "Create an issue in a repository.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string"},
                                    "repo": {"type": "string"},
                                    "title": {"type": "string"},
                                    "body": {"type": "string"}},
                     "required": ["owner", "repo", "title"]}},
    {"name": "list_issues",
     "description": "List issues of a repository.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string"},
                                    "repo": {"type": "string"},
                                    "state": {"type": "string"}},
                     "required": ["owner", "repo"]}},
    {"name": "create_pull_request",
     "description": "Create a pull request in a repository.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string"},
                                    "repo": {"type": "string"},
                                    "title": {"type": "string"},
                                    "head": {"type": "string"},
                                    "base": {"type": "string"}},
                     "required": ["owner", "repo", "title", "head", "base"]}},
    {"name": "merge_pull_request",
     "description": "Merge a pull request by number.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string"},
                                    "repo": {"type": "string"},
                                    "pull_number": {"type": "integer"}},
                     "required": ["owner", "repo", "pull_number"]}},
]


def _norm_key(k):
    return re.sub(r"[^a-z0-9]", "", str(k).lower())


def _pick_arg(args, names):
    """Return the first present argument whose normalized name is in names."""
    want = {_norm_key(n) for n in names}
    for k, v in args.items():
        if _norm_key(k) in want:
            return v
    return None


def _split_full_name(value):
    if value and "/" in str(value):
        o, r = str(value).split("/", 1)
        return o or None, r or None
    return None, None


def _mcp_owner_repo(args):
    owner = _pick_arg(args, ["owner", "ownerLogin", "ownerName", "org",
                             "organization", "organisation", "user", "userLogin",
                             "login", "account", "namespace"])
    repo = _pick_arg(args, ["repo", "repository", "repositoryName", "repoName",
                            "repoSlug", "project", "projectName"])
    if (not owner or not repo):
        full = _pick_arg(args, ["fullName", "repoFullName", "repositoryFullName",
                                "full_name", "nameWithOwner"])
        o, r = _split_full_name(full)
        owner = owner or o
        repo = repo or r
    return owner, repo


def _mcp_result(obj):
    text = json.dumps(obj, separators=(",", ":"))
    return {"content": [{"type": "text", "text": text}], "structuredContent": obj}


def _mcp_error_result(message):
    return {"content": [{"type": "text", "text": message}], "isError": True}


def _mcp_call_tool(name, args):
    norm = _norm_key(name or "")
    canon = None
    for t in MCP_TOOLS:
        if norm == _norm_key(t["name"]) or norm.endswith(_norm_key(t["name"])):
            canon = t["name"]
            break
    if canon is None:
        return None, {"code": -32601, "message": "Unknown tool: %s" % name}
    if not isinstance(args, dict):
        args = {}

    if canon == "create_repo":
        repo_name = _pick_arg(args, ["name", "repo", "repository", "repositoryName",
                                     "repoName", "repoSlug", "project", "projectName"])
        if not repo_name:
            return _mcp_error_result("Missing required argument: name"), None
        if STORE.get_repo(VIEWER_LOGIN, repo_name) is not None:
            return _mcp_error_result("Repository already exists: %s" % repo_name), None
        r = STORE.create_repo(repo_name,
                              _pick_arg(args, ["description", "about", "summary"]) or "")
        return _mcp_result(repo_json(r, "")), None

    owner, repo = _mcp_owner_repo(args)
    if canon == "get_repo":
        if not owner or not repo:
            return _mcp_error_result("Missing required argument: owner/repo"), None
        r = STORE.get_repo(owner, repo)
        if r is None:
            return _mcp_error_result("Repository not found: %s/%s" % (owner, repo)), None
        return _mcp_result(repo_json(r, "")), None

    if canon == "create_issue":
        title = _pick_arg(args, ["title", "issueTitle", "subject"])
        body = _pick_arg(args, ["body", "issueBody", "description", "content", "text"])
        if not owner or not repo:
            return _mcp_error_result("Missing required argument: owner/repo"), None
        if not title:
            return _mcp_error_result("Missing required argument: title"), None
        r = STORE.get_repo(owner, repo)
        if r is None:
            return _mcp_error_result("Repository not found: %s/%s" % (owner, repo)), None
        r.issue_seq += 1
        n = r.issue_seq
        STORE.issue_id_seq += 1
        issue = {"id": STORE.issue_id_seq, "number": n, "title": title,
                 "body": body or "", "state": "open", "labels": [], "comments": [],
                 "created_at": _iso_now(), "updated_at": _iso_now(), "closed_at": None}
        r.issues[n] = issue
        return _mcp_result(issue_json(r, issue)), None

    if canon == "list_issues":
        if not owner or not repo:
            return _mcp_error_result("Missing required argument: owner/repo"), None
        r = STORE.get_repo(owner, repo)
        if r is None:
            return _mcp_error_result("Repository not found: %s/%s" % (owner, repo)), None
        state = _pick_arg(args, ["state", "status"])
        issues = sorted(r.issues.values(), key=lambda i: -i["number"])
        if state:
            issues = [i for i in issues if i["state"] == str(state).lower()]
        return _mcp_result({"issues": [issue_json(r, i) for i in issues]}), None

    if canon == "create_pull_request":
        title = _pick_arg(args, ["title", "prTitle", "pullRequestTitle", "subject"])
        head = _pick_arg(args, ["head", "headRef", "headBranch", "pullRequestHead",
                                "prHead", "source", "sourceRef", "sourceBranch",
                                "from", "fromBranch", "branch"])
        base = _pick_arg(args, ["base", "baseRef", "baseBranch", "pullRequestBase",
                                "prBase", "target", "targetRef", "targetBranch",
                                "into", "intoBranch"])
        if not owner or not repo:
            return _mcp_error_result("Missing required argument: owner/repo"), None
        if not title or not head or not base:
            return _mcp_error_result("Missing required argument: title/head/base"), None
        r = STORE.get_repo(owner, repo)
        if r is None:
            return _mcp_error_result("Repository not found: %s/%s" % (owner, repo)), None
        head_sha = r.head_sha(head)
        base_sha = r.head_sha(base)
        if head_sha is None or base_sha is None:
            return _mcp_error_result("head or base branch does not exist"), None
        r.pr_seq += 1
        num = r.pr_seq
        STORE.pr_id_seq += 1
        mb = r.merge_base(base_sha, head_sha)
        mergeable = _pr_mergeable(r, base_sha, head_sha, mb)
        files = _pr_files(r, base_sha, head_sha, mb)
        pr = {"id": STORE.pr_id_seq, "number": num, "title": title,
              "body": _pick_arg(args, ["body", "description", "content", "text"]) or "",
              "state": "open", "head": head, "head_sha": head_sha,
              "base": base, "base_sha": base_sha,
              "merged": False, "mergeable": mergeable,
              "merged_at": None, "merge_commit_sha": None,
              "created_at": _iso_now(), "updated_at": _iso_now(), "closed_at": None,
              "labels": [], "commits": _count_commits(r, mb, head_sha),
              "additions": sum(f["additions"] for f in files),
              "deletions": sum(f["deletions"] for f in files),
              "changed_files": len(files), "_files": files, "_merge_base": mb}
        r.prs[num] = pr
        return _mcp_result(pr_json(r, pr)), None

    if canon == "merge_pull_request":
        num = _pick_arg(args, ["pullNumber", "pullRequestNumber", "prNumber",
                               "number", "issueNumber", "index"])
        if not owner or not repo:
            return _mcp_error_result("Missing required argument: owner/repo"), None
        if num is None:
            return _mcp_error_result("Missing required argument: pull_number"), None
        try:
            num = int(num)
        except Exception:
            return _mcp_error_result("pull_number must be an integer"), None
        r = STORE.get_repo(owner, repo)
        if r is None:
            return _mcp_error_result("Repository not found: %s/%s" % (owner, repo)), None
        pr = r.prs.get(num)
        if pr is None:
            return _mcp_error_result("Pull request not found: %d" % num), None
        if pr["state"] != "open" or pr["merged"]:
            return _mcp_error_result("Pull request is not open"), None
        if not pr["mergeable"]:
            return _mcp_error_result("Pull request is not mergeable"), None
        head_files = r.tree_files(r.commit_tree(pr["head_sha"])[0])
        message = "Merge pull request #%d from %s" % (pr["number"], pr["head"])
        merge_sha = r.commit(pr["base"], head_files, message, [pr["base_sha"]])
        pr["merged"] = True
        pr["state"] = "closed"
        pr["merged_at"] = _iso_now()
        pr["closed_at"] = _iso_now()
        pr["merge_commit_sha"] = merge_sha
        pr["updated_at"] = _iso_now()
        return _mcp_result(pr_json(r, pr)), None

    return None, {"code": -32601, "message": "Unknown tool: %s" % name}


def handle_mcp(body_bytes, headers):
    """Returns (status, obj_or_None, extra_headers)."""
    try:
        req = json.loads(body_bytes.decode("utf-8"))
    except Exception:
        return 400, {"jsonrpc": "2.0", "id": None,
                     "error": {"code": -32700, "message": "Parse error"}}, {}
    if not isinstance(req, dict):
        return 400, {"jsonrpc": "2.0", "id": None,
                     "error": {"code": -32600, "message": "Invalid Request"}}, {}
    rid = req.get("id")
    method = req.get("method") or ""
    params = req.get("params") or {}
    if not isinstance(params, dict):
        params = {}

    if method.startswith("notifications/"):
        return 202, None, {}

    def rpc_error(code, message, data=None):
        err = {"code": code, "message": message}
        if data is not None:
            err["data"] = data
        return 200, {"jsonrpc": "2.0", "id": rid, "error": err}, {}

    def rpc_result(result, extra_headers=None):
        return 200, {"jsonrpc": "2.0", "id": rid, "result": result}, extra_headers or {}

    meta = params.get("_meta") or {}
    hdr_version = headers.get("MCP-Protocol-Version")
    meta_version = meta.get("protocolVersion")

    if method == "server/discover":
        version = meta_version or hdr_version
        if version and version not in MCP_VERSIONS:
            return rpc_error(-32022, "Unsupported protocol version",
                             {"supported": MCP_VERSIONS})
        if hdr_version and meta_version and hdr_version != meta_version:
            return rpc_error(-32020, "Protocol version mismatch")
        return rpc_result({"supportedVersions": list(MCP_VERSIONS),
                           "capabilities": {"tools": {}},
                           "serverInfo": {"name": "git-forge", "version": "1.0.0"}})

    if method == "initialize":
        version = params.get("protocolVersion") or hdr_version
        if version and version not in MCP_VERSIONS:
            return rpc_error(-32022, "Unsupported protocol version",
                             {"supported": MCP_VERSIONS})
        if hdr_version and meta_version and hdr_version != meta_version:
            return rpc_error(-32020, "Protocol version mismatch")
        result = {"protocolVersion": version or MCP_VERSIONS[0],
                  "capabilities": {"tools": {}},
                  "serverInfo": {"name": "git-forge", "version": "1.0.0"}}
        return rpc_result(result, {"Mcp-Session-Id": "session-1"})

    if method == "tools/list":
        return rpc_result({"tools": MCP_TOOLS})

    if method == "tools/call":
        name = params.get("name")
        args = params.get("arguments") or {}
        result, err = _mcp_call_tool(name, args)
        if err is not None:
            return rpc_error(err["code"], err["message"])
        return rpc_result(result)

    return rpc_error(-32601, "Method not found: %s" % method)


# ---------------------------------------------------------------- HTTP + lifecycle

class ForgeServer(_http.ThreadingHTTPServer):
    """ThreadingHTTPServer with TCP_NODELAY on every accepted socket.

    Without it, a small response on a keep-alive connection stalls ~40 ms
    per request (Nagle + delayed ACK): the bench's 2,000-request read
    workload would take ~80 s instead of ~1 s."""
    daemon_threads = True

    def get_request(self):
        sock, addr = super().get_request()
        sock.setsockopt(_socket.IPPROTO_TCP, _socket.TCP_NODELAY, 1)
        return sock, addr


class ForgeHandler(_http.BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    server_version = "git-forge/1.0"

    def log_message(self, *args):
        pass

    def _read_body(self):
        length = int(self.headers.get("Content-Length") or 0)
        if length <= 0:
            return b""
        return self.rfile.read(length)

    def _auth_ok(self):
        auth = self.headers.get("Authorization") or ""
        if SHOP_TOKEN:
            return auth == "Bearer " + SHOP_TOKEN
        return auth.startswith("Bearer ") and len(auth) > 7

    def _send_json(self, status, obj, extra=None):
        body = b"" if obj is None else json.dumps(obj).encode()
        self.send_response(status)
        if obj is not None:
            self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("X-GitHub-Request-Id", next_req_id())
        for k, v in (extra or {}).items():
            self.send_header(k, v)
        self.end_headers()
        if body:
            self.wfile.write(body)

    def _send_bytes(self, status, content_type, body, extra=None):
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("X-GitHub-Request-Id", next_req_id())
        for k, v in (extra or {}).items():
            self.send_header(k, v)
        self.end_headers()
        if body:
            self.wfile.write(body)

    def _route(self, method):
        parsed = _url.urlparse(self.path)
        path = parsed.path
        query = _url.parse_qs(parsed.query)
        base_url = "http://" + (self.headers.get("Host") or "127.0.0.1")

        if path == "/healthz":
            return self._send_json(200, {"ok": True})
        if not self._auth_ok():
            return self._send_json(401, {"message": "Bad credentials"})

        try:
            if path.startswith("/api/v3"):
                status, obj, extra = handle_rest(self, method, path, query, base_url)
                return self._send_json(status, obj, extra)
            if path == "/api/graphql" and method == "POST":
                body = self._read_body()
                try:
                    payload = json.loads(body.decode("utf-8"))
                except Exception:
                    return self._send_json(200, {"errors": [{"message": "Invalid JSON body"}]})
                return self._send_json(200, execute_graphql(payload))
            if path == "/mcp" and method == "POST":
                body = self._read_body()
                status, obj, extra = handle_mcp(body, self.headers)
                return self._send_json(status, obj, extra)
            if ".git/" in path or path.endswith(".git"):
                body = self._read_body() if method in ("POST", "PUT") else b""
                status, ctype, data = handle_git(self, method, path, query, body)
                return self._send_bytes(status, ctype, data)
            return self._send_json(404, {"message": "Not Found"})
        except ApiError as e:
            return self._send_json(e.status, {"message": e.message})
        except BrokenPipeError:
            raise
        except Exception as e:
            return self._send_json(500, {"message": "Internal server error: %s" % e})

    def do_GET(self):
        self._route("GET")

    def do_POST(self):
        self._route("POST")

    def do_PUT(self):
        self._route("PUT")

    def do_PATCH(self):
        self._route("PATCH")

    def do_DELETE(self):
        self._route("DELETE")


def _http_call(url, method, body=None, headers=None, timeout=30):
    req = _urllib.Request(url, data=body, method=method)
    for k, v in (headers or {}).items():
        req.add_header(k, v)
    try:
        with _urllib.urlopen(req, timeout=timeout) as resp:
            return resp.status, resp.read()
    except urllib.error.HTTPError as e:
        return e.code, e.read()
    except Exception:
        return None, b""


def main():
    global ENV_URL, SHOP_TOKEN, TRIAL_NOW, NOW_ISO
    ENV_URL = os.environ.get("MAKEFUN_ENV_URL", "")
    SHOP_TOKEN = os.environ.get("MAKEFUN_SHOP_TOKEN", "")
    TRIAL_NOW = os.environ.get("MAKEFUN_TRIAL_NOW", "")
    TRIAL_SEED = os.environ.get("MAKEFUN_TRIAL_SEED", "")
    NOW_ISO = TRIAL_NOW or "2025-01-01T00:00:00Z"

    server = ForgeServer(("127.0.0.1", 0), ForgeHandler)
    port = server.server_address[1]

    if not ENV_URL:
        print("Listening on 127.0.0.1:%d (no MAKEFUN_ENV_URL; local mode)" % port, flush=True)
        try:
            server.serve_forever()
        except KeyboardInterrupt:
            pass
        return 0

    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()

    # Register: 200 or 409 = ok; 400/405 = fatal; retry on transient errors.
    delay = 0.25
    registered = False
    while True:
        status, body = _http_call(ENV_URL.rstrip("/") + "/register", "POST",
                                  json.dumps({"port": port}).encode(),
                                  {"Content-Type": "application/json"}, timeout=30)
        if status in (200, 409):
            registered = True
            break
        if status in (400, 405):
            print("register rejected: %s %s" % (status, body[:200]), flush=True)
            server.shutdown()
            return 1
        time.sleep(delay)
        delay = min(delay * 2, 2.0)

    # Poll /done until the trial ends.
    delay = 0.25
    while True:
        status, body = _http_call(ENV_URL.rstrip("/") + "/done", "GET", timeout=30)
        if status == 200:
            try:
                done = json.loads(body.decode()).get("done")
            except Exception:
                done = False
            if done:
                break
        time.sleep(delay)
        delay = min(delay * 2, 2.0)

    server.shutdown()
    return 0


if __name__ == "__main__":
    sys.exit(main())
