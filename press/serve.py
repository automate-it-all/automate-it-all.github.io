#!/usr/bin/env python3
"""serve.py — the live front-end for a docs-as-records decision page.

THIS FILE IS VENDORED. `docs-as-records page render` copies it, byte for byte,
to `<corpus>/page/serve.py`, and it is meant to be COMMITTED there. That is the
whole point of it: the person who opens the page must not need the framework
installed, on their PATH, or even on the machine. A checkout and a Python is the
whole dependency list.

    python3 <corpus>/page/serve.py            # serve + open a browser
    python3 <corpus>/page/serve.py --no-open  # serve only
    python3 <corpus>/page/serve.py --port 8791

Do not edit the copy. It is overwritten on the next render, and the render gate
compares it byte for byte — a hand-edit is reported as a page that does not
reproduce. Fix the original in the framework and re-render.

WHAT IT ADDS, AND WHAT IT REFUSES TO ADD
----------------------------------------
The rendered page works with no server at all: opened over `file://` it shows
everything and hands you a JSON patch to paste back. That path stays. This
server exists for the one thing a `file://` page cannot do — **write what you
type to disk, as you type it** — and it writes ONLY what the static round-trip
would have written anyway:

  * a `note` record  — your margin note on an item. Autosaved, and it clears
    nothing. Read it in `git status` and commit it.

  * an `answer` record — your verdict, the same shape `page apply` writes.

  * a hand-added `record` and its picture — the row for a thing the corpus
    holds no record for. `Edit row` says one again, its pictures kept.

It never edits a record an agent wrote, never mutates a `status`, never renders
and never commits.

A record holds one note and one answer, both overwritten in place.

Killed mid-session, what you had already typed is on disk.

The corpus is not configured, it is DERIVED: this file sits at
`<corpus>/page/serve.py`, so the board is its grandparent and every copy is
byte-identical.

The rows are wherever `records/` RESOLVES to. A board symlinking a second
corpus's `records/` writes verdicts beside the record, never beside the page.
"""
from __future__ import annotations

import argparse
import base64
import binascii
import hashlib
import http.client
import json
import re
import socket
import subprocess
import sys
import threading
import webbrowser
from datetime import date
from html import escape
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, unquote, urlparse

# Two levels up for the page; `records/` RESOLVED for the corpus that owns the
# rows, so an answer lands beside its record.
PAGE_DIR = Path(__file__).resolve().parent
EPIC = PAGE_DIR.parent
RECORD_DIR = (EPIC / "records").resolve()
CORPUS = RECORD_DIR.parent if RECORD_DIR.is_dir() else EPIC
ANSWER_DIR = CORPUS / "answers"
NOTE_DIR = CORPUS / "notes"

def _git_name() -> str:
    """Who answered, from the machine's git identity.

    Nothing on the page asks for a name, so this is the only place one comes from.
    """
    try:
        out = subprocess.run(["git", "config", "user.name"], cwd=CORPUS, check=False,
                             capture_output=True, text=True, timeout=5)
    except (OSError, subprocess.SubprocessError):
        return ""
    return out.stdout.strip()


GIT_NAME = _git_name()

HEALTH_MARKER = "docs-as-records-page"
#: `serve-all`'s own URL when it launched this child, else "". `--home` sets it.
HOME = ""
VERDICTS = ("accepted", "rejected", "answered", "needs-ai-work", "more-info", "challenged")
#: The verdicts that hand a row back to a pass. Same tuple as `page.REOPENING`.
REOPENING = ("needs-ai-work", "more-info", "challenged")

MIME = {
    ".html": "text/html; charset=utf-8", ".css": "text/css; charset=utf-8",
    ".js": "text/javascript; charset=utf-8", ".json": "application/json",
    ".png": "image/png", ".jpg": "image/jpeg", ".jpeg": "image/jpeg",
    ".gif": "image/gif", ".webp": "image/webp", ".svg": "image/svg+xml",
    ".pdf": "application/pdf", ".txt": "text/plain; charset=utf-8",
    ".md": "text/plain; charset=utf-8", ".yaml": "text/plain; charset=utf-8",
}


# --------------------------------------------------------------------------- #
# YAML, the two-way sliver of it these records actually use
#
# A record here is flat scalars plus one `body: |` block plus a two-level
# `meta:` / `relations:` map. Vendoring a YAML library to read that back would
# defeat the purpose of the file, so: use PyYAML when the interpreter happens to
# have it, and fall back to a parser that handles exactly the shape we emit.
# --------------------------------------------------------------------------- #
def _yaml_scalar(v) -> str:
    if v is True:
        return "true"
    if v is False:
        return "false"
    if v is None or v == "":
        return "''"
    if isinstance(v, (int, float)):
        return repr(v)
    # Single-quoting with doubled quotes is safe for every scalar YAML admits on
    # one line, which is all we emit — multi-line values go through _yaml_block.
    return "'" + str(v).replace("'", "''") + "'"


def _yaml_block(key: str, text: str, indent: int = 0) -> str:
    """`key: |` with `text` as a literal block. Preserves the body verbatim."""
    pad = " " * indent
    body = str(text).replace("\r\n", "\n").replace("\r", "\n").rstrip("\n")
    lines = body.split("\n")
    # A block scalar whose first content line is itself indented is ambiguous
    # without an explicit indentation indicator — YAML would read the extra
    # spaces as the block's own indentation and silently strip them.
    first = next((ln for ln in lines if ln.strip()), "")
    head = f"{pad}{key}: |2" if first[:1] in (" ", "\t") else f"{pad}{key}: |"
    return "\n".join([head] + [(f"{pad}  {ln}").rstrip() for ln in lines])


def _dump_record(doc: dict, path: Path) -> None:
    """Write a record. Key order is fixed and the output is stable, so re-saving
    a note whose text did not change produces the same bytes."""
    out = ["meta:",
           f"  format: {_yaml_scalar(doc['meta']['format'])}",
           f"  kind: {_yaml_scalar(doc['meta']['kind'])}"]
    for key in ("id", "for", "title", "status", "group", "tldr", "verdict", "chose",
                "by", "at"):
        if doc.get(key) not in (None, ""):
            out.append(f"{key}: {_yaml_scalar(doc[key])}")
    if str(doc.get("body") or "").strip():
        out.append(_yaml_block("body", doc["body"]))
    if doc.get("evidence"):
        out.append("evidence:")
        out.extend(f"  - {_yaml_scalar(p)}" for p in doc["evidence"])
    rel = doc.get("relations") or {}
    if rel:
        out.append("relations:")
        for typ in sorted(rel):
            targets = rel[typ] or []
            if not targets:
                continue
            out.append(f"  {typ}:")
            out.extend(f"    - {_yaml_scalar(t)}" for t in targets)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(out) + "\n", encoding="utf-8")


def _split_flow(body: str) -> list[str]:
    """Top-level commas of a flow collection, respecting quotes and nesting."""
    out, depth, quote, cur = [], 0, "", []
    for ch in body:
        if quote:
            cur.append(ch)
            if ch == quote:
                quote = ""
            continue
        if ch in "'\"":
            quote = ch
        elif ch in "[{":
            depth += 1
        elif ch in "]}":
            depth -= 1
        elif ch == "," and depth == 0:
            out.append("".join(cur))
            cur = []
            continue
        cur.append(ch)
    tail = "".join(cur).strip()
    if tail:
        out.append(tail)
    return [p.strip() for p in out if p.strip()]


def _unquote_scalar(s: str):
    s = s.strip()
    if len(s) >= 2 and s[0] == s[-1] and s[0] in "'\"":
        inner = s[1:-1]
        return inner.replace("''", "'") if s[0] == "'" else inner
    # Flow collections: this server never writes them, but a hand-authored or
    # third-party record may, and silently reading `{format: …, kind: answer}` as
    # a string is how an answer becomes invisible on the no-PyYAML path.
    if len(s) >= 2 and s[0] == "{" and s[-1] == "}":
        out = {}
        for part in _split_flow(s[1:-1]):
            k, sep, v = part.partition(":")
            if sep:
                out[k.strip()] = _unquote_scalar(v)
        return out
    if len(s) >= 2 and s[0] == "[" and s[-1] == "]":
        return [_unquote_scalar(p) for p in _split_flow(s[1:-1])]
    if s in ("true", "false"):
        return s == "true"
    return s


def _mini_parse(text: str) -> dict:
    """Read back the shape `_dump_record` writes (and PyYAML's equivalent).

    Deliberately narrow: top-level scalars, one literal block, and one level of
    nesting under `meta:` / `relations:`. Anything richer is a record this server
    did not write, and the only fields it needs from those are the flat ones.
    """
    doc: dict = {}
    lines = text.replace("\r\n", "\n").split("\n")
    i, n = 0, len(lines)
    while i < n:
        raw = lines[i]
        i += 1
        if not raw.strip() or raw.lstrip().startswith("#") or raw[:1].isspace():
            continue
        m = re.match(r"^([A-Za-z_][\w-]*):\s*(.*)$", raw)
        if not m:
            continue
        key, val = m.group(1), m.group(2).strip()
        if val.startswith("|"):
            block, strip = [], None
            while i < n:
                ln = lines[i]
                if ln.strip() and not ln[:1].isspace():
                    break
                if strip is None and ln.strip():
                    strip = len(ln) - len(ln.lstrip(" "))
                block.append(ln[strip:] if strip and ln[:strip].strip() == "" else ln.strip())
                i += 1
            # `|` is CLIP chomping: exactly one trailing newline, however many the
            # file carried. Getting this wrong makes every read-back differ from
            # PyYAML's by one character, which is the kind of drift that only shows
            # up as a spurious "the note changed" three weeks later.
            text = "\n".join(block).rstrip("\n")
            doc[key] = text + "\n" if text else ""
        elif val == "":
            sub: dict = {}
            cur = None
            while i < n:
                ln = lines[i]
                if ln.strip() and not ln[:1].isspace():
                    break
                s = ln.strip()
                i += 1
                if not s:
                    continue
                if s.startswith("- "):
                    if cur is not None:
                        sub.setdefault(cur, []).append(_unquote_scalar(s[2:]))
                    continue
                sm = re.match(r"^([A-Za-z_][\w-]*):\s*(.*)$", s)
                if not sm:
                    continue
                if sm.group(2).strip():
                    sub[sm.group(1)] = _unquote_scalar(sm.group(2))
                    cur = None
                else:
                    cur = sm.group(1)
                    sub[cur] = []
            doc[key] = sub
        else:
            doc[key] = _unquote_scalar(val)
    return doc


def _load_record(path: Path) -> dict:
    text = path.read_text(encoding="utf-8")
    try:
        import yaml  # optional shortcut; _mini_parse is the contract, not this
    except ImportError:
        return _mini_parse(text)
    try:
        doc = yaml.safe_load(text)
    except Exception:
        return _mini_parse(text)
    return doc if isinstance(doc, dict) else {}


def _slug(rid: str) -> str:
    return re.sub(r"[^A-Za-z0-9._-]", "_", str(rid))


def _read_kind(directory: Path, kind: str) -> list[dict]:
    if not directory.is_dir():
        return []
    out = []
    for p in sorted(directory.glob("*.yaml")):
        doc = _load_record(p)
        if str((doc.get("meta") or {}).get("kind") or "").lower() == kind:
            out.append(doc)
    return out


# --------------------------------------------------------------------------- #
# state
# --------------------------------------------------------------------------- #
_WRITE_LOCK = threading.Lock()


def _rev(*parts) -> str:
    """Twelve characters standing for what the writer last saw on this row.

    Content and never mtime: a re-render moves the clock without changing a word,
    and a refusal for that teaches the reader to ignore refusals.
    """
    joined = "\n".join(str(p or "") for p in parts)
    return hashlib.sha1(joined.encode("utf-8")).hexdigest()[:12]


def _rev_now(target: str, kind: str) -> str:
    """The rev `/state` serves for this row, which is the one the reader holds.

    Asked of `read_state`, never of the canonical path: eight rows on two real
    boards answer at `ANS-<id>-2.yaml`, so a canonical read refuses them forever.

    Hashing what was SENT disagrees by the newline a block scalar reads back.
    """
    state = read_state()
    if kind == "note":
        return (state["notes"].get(target) or {}).get("rev", "")
    return ((state["answers"].get(target) or [{}])[0] or {}).get("rev", "")


def corpus_stamp(epic: Path | None = None, *, sub: str = "records",
                 pat: str = "*.yaml") -> dict:
    """What the corpus says now, for a tab to compare against what it drew.

    Content and never mtime: a clone gives every file a fresh clock, and a page
    crying stale on a checkout is noise.

    7.4ms over 361 records, against `/state`'s own 14-44ms.

    `epic` is what lets the RENDERER bake the same number by importing this, so
    the two halves of the comparison cannot drift apart.

    `sub`/`pat` are what give the reading view a stamp: it is drawn from
    `atlas/*.json`, so the records digest cannot answer for it.
    """
    root = (epic or EPIC) / sub
    digest, n = hashlib.sha1(), 0
    for path in sorted(root.rglob(pat)):
        # Relative: the renderer may hold the corpus by a relative path, and an
        # absolute one there would put the two stamps permanently at odds.
        digest.update(str(path.relative_to(root)).encode("utf-8"))
        try:
            digest.update(path.read_bytes())
        except OSError:
            continue
        n += 1
    return {"n": n, "h": digest.hexdigest()[:12]}


# Two tabs used to overwrite each other in silence, both told `ok`. A record still
# holds ONE note; the losing write is refused now.
STALE = ("somebody else saved this {} since you loaded — reload to read theirs. "
         "Nothing was written, and what you typed is still in the box")


def read_state() -> dict:
    """What is on disk right now, keyed by the record each write is ABOUT.

    Read fresh on every request rather than cached at startup: the corpus is a
    directory of files, an agent may be writing to it in another terminal, and a
    stale snapshot is how a cockpit silently reverts somebody else's work.
    """
    notes = {}
    for doc in _read_kind(NOTE_DIR, "note"):
        tgt = str(doc.get("for") or "")
        if tgt:
            notes[tgt] = {"body": str(doc.get("body") or ""), "at": str(doc.get("at") or ""),
                          "by": str(doc.get("by") or ""),
                          "rev": _rev(doc.get("body"))}
    answers: dict[str, list] = {}
    for doc in _read_kind(ANSWER_DIR, "answer"):
        tgt = str(doc.get("for") or "")
        if not tgt:
            continue
        answers.setdefault(tgt, []).append({
            "id": str(doc.get("id") or ""), "verdict": str(doc.get("verdict") or ""),
            "chose": str(doc.get("chose") or ""),
            "by": str(doc.get("by") or ""), "at": str(doc.get("at") or ""),
            "body": str(doc.get("body") or ""),
            "rev": _rev(doc.get("verdict"), doc.get("body"), doc.get("chose")),
            "supersedes": [str(s) for s in ((doc.get("relations") or {}).get("supersedes") or [])],
        })
    for tgt, lst in answers.items():
        superseded = {s for a in lst for s in a["supersedes"]}
        live = [a for a in lst if a["id"] not in superseded]
        rest = [a for a in lst if a["id"] in superseded]
        answers[tgt] = sorted(live, key=lambda a: a["id"]) + sorted(rest, key=lambda a: a["id"])
    return {"ok": True, "epic": EPIC.name, "notes": notes, "answers": answers,
            "home": HOME, "today": date.today().isoformat(), "corpus": corpus_stamp(),
            "atlas": corpus_stamp(sub="atlas", pat="*.json")}


def _first_picture(doc) -> str:
    """The record's first `evidence:` image, corpus-relative, in any of the three
    shapes the field accepts."""
    raw = doc.get("evidence") or []
    if isinstance(raw, (str, bytes)):
        raw = [raw]
    for item in raw:
        path = str(item.get("path") or item.get("src") or "") if isinstance(item, dict) \
            else str(item)
        if path.lower().endswith((".png", ".jpg", ".jpeg", ".webp", ".gif")):
            return path
    return ""


def sweep() -> dict:
    """Which rows a sweep collects if one starts now, before one does.

    The rule is `queue.unanswered`, re-stated because this file imports nothing.

    `mute` is the other half: a row sent back with no words is collected by nobody.
    """
    state = read_state()
    taken, mute = [], []
    for path in sorted(RECORD_DIR.rglob("*.yaml")):
        doc = _load_record(path)
        rid = str(doc.get("id") or "")
        if not rid:
            continue
        live = (state["answers"].get(rid) or [None])[0] or {}
        verdict = str(live.get("verdict") or "")
        sent_back = verdict in REOPENING
        # Done and Reject clear the row, so the note beside one reads as a remark.
        if live and not sent_back:
            continue
        text = str((live if sent_back else state["notes"].get(rid) or {}).get("body")
                   or "").strip()
        row = {"id": rid, "title": str(doc.get("title") or rid), "verdict": verdict,
               "why": ("sent back" if sent_back else "margin note"), "text": text,
               # A row the render has never seen is drawn by the panel or by nothing.
               "shot": _first_picture(doc)}
        if text and text != str(doc.get("answered") or "").strip():
            taken.append(row)
        elif sent_back:
            mute.append(row)
    return {"ok": True, "taken": taken, "mute": mute}


def _hit_line(text: str, needle: str) -> str:
    """The words around a match, with the YAML holding them taken off.

    A raw line reads `status: open` or `path: 'A/B/C'`, and a 200-character cut
    measured at the line start drops the searched word itself.
    """
    line = " ".join(next((ln for ln in text.splitlines()
                          if needle in ln.lower()), "").split())
    body = re.sub(r"^-?\s*[A-Za-z_][\w.-]*:\s*[|>]?[-+0-9]*\s*", "", line)
    body = body.rstrip(",").strip("'\"").strip()
    # A one-word value keeps its key: `open` alone says less than `status: open`.
    if " " in body and needle in body.lower():
        line = body
    at = line.lower().find(needle)
    if len(line) <= 200 or at < 0:
        return line[:200]
    start = max(0, at - 60)
    end = start + 200
    return ("…" if start else "") + line[start:end] + ("…" if end < len(line) else "")


def deep_find(q: str, limit: int = 300) -> dict:
    """Every word of every record, note and answer, for a board that read the
    summaries and answered for the whole corpus.

    The find box matches `data-find`, poured from what a shut card shows, so it
    answers `0 of 361` for a word in a body.
    #
    Each hit carries the line the word is on, so the reader sees the match without
    opening the row.
    """
    needle = " ".join(str(q or "").split()).lower()
    if not needle:
        return {"ok": False, "error": "nothing to look for"}
    hits, scanned, cut = {}, 0, False
    for where, root in (("record", RECORD_DIR), ("note", NOTE_DIR),
                        ("answer", ANSWER_DIR)):
        for path in sorted(root.rglob("*.yaml")):
            scanned += 1
            try:
                text = path.read_text(encoding="utf-8")
            except OSError:
                continue
            if needle not in text.lower():
                continue
            doc = _load_record(path)
            # A note and an answer are ABOUT a row; the board holds the row, so
            # `for:` is the id with a card to light up.
            rid = str((doc.get("id") if where == "record" else doc.get("for")) or "")
            if not rid or rid in hits:
                continue
            if len(hits) >= limit:
                cut = True
                continue
            hits[rid] = {"id": rid, "where": where, "line": _hit_line(text, needle)}
    return {"ok": True, "q": needle, "scanned": scanned, "cut": cut,
            "hits": sorted(hits.values(), key=lambda h: h["id"])}


def write_note(target: str, body: str, by: str = "", rev: str | None = None) -> dict:
    """Autosaved margin note. Emptying it REMOVES the record — a note you deleted
    should not survive as an empty file for you to wonder about in `git status`.

    Send the `/state` rev you read and a note that moved underneath you is
    refused. Omit it and the write lands.
    """
    path = NOTE_DIR / f"NOTE-{_slug(target)}.yaml"
    with _WRITE_LOCK:
        if rev is not None and rev != _rev_now(target, "note"):
            return {"ok": False, "stale": True, "error": STALE.format("note")}
        if not str(body).strip():
            if path.exists():
                path.unlink()
            return {"ok": True, "removed": True, "rev": "",
                    "path": f"notes/{path.name}"}
        doc = {
            "meta": {"format": "docs-as-records", "kind": "note"},
            "id": f"NOTE-{target}", "for": target,
            "title": f"note — {target}",
            "by": by, "at": date.today().isoformat(), "body": body,
            "relations": {"references": [target]},
        }
        _dump_record(doc, path)
        now = _rev_now(target, "note")
    return {"ok": True, "rev": now, "path": f"notes/{path.name}"}


def _sole_answer(target: str, keep: Path | None) -> list[str]:
    """Drop every other answer file addressing `target`, and name what went.

    Six files for six clicks is what the reader met; the history is in git.
    `keep=None` keeps none, which is how a verdict comes off.
    """
    gone = []
    for path in ANSWER_DIR.glob("*.yaml") if ANSWER_DIR.is_dir() else ():
        if path == keep:
            continue
        doc = _load_record(path)
        if str((doc.get("meta") or {}).get("kind") or "").lower() == "answer" \
                and str(doc.get("for") or "") == target:
            path.unlink()
            gone.append(path.name)
    return gone


def clear_answer(target: str, rev: str | None = None) -> dict:
    """Put a record back to unanswered, the way emptying a note removes it.

    Signing again supersedes a verdict; a row that never had one had no way
    back, and `mark all` writes one behind a single confirm.
    """
    with _WRITE_LOCK:
        if rev is not None and rev != _rev_now(target, "answer"):
            return {"ok": False, "stale": True, "error": STALE.format("verdict")}
        gone = _sole_answer(target, None)
    return {"ok": True, "removed": bool(gone), "rev": "",
            "path": f"answers/{gone[0]}" if gone else ""}


def write_answer(target: str, verdict: str, by: str, body: str, title: str = "",
                 rev: str | None = None, chose: str = "") -> dict:
    """The verdict, as ONE file per record that later clicks overwrite.

    An empty body keeps what the human typed, so clicking a verdict never
    costs a comment. Only typing in the box replaces one.

    `chose` is one of the record's own options, verbatim: the accept is the only
    click that says which one won, and `queue promote` refuses a row without it.

    `rev` refuses a verdict written over one the writer never saw.
    """
    if verdict not in VERDICTS:
        return {"ok": False, "error": f"verdict {verdict!r} is not one of {', '.join(VERDICTS)}"}
    with _WRITE_LOCK:
        aid = f"ANS-{target}"
        path = ANSWER_DIR / f"{_slug(aid)}.yaml"
        if rev is not None and rev != _rev_now(target, "answer"):
            return {"ok": False, "stale": True, "error": STALE.format("verdict")}
        if not str(body).strip() or not str(chose).strip():
            prior = (read_state()["answers"].get(target) or [None])[0]
            # Same rule for both: a click that carries neither keeps what the human
            # already typed and already picked.
            body = body if str(body).strip() else (prior or {}).get("body", body)
            chose = chose if str(chose).strip() else (prior or {}).get("chose", chose)
        doc = {
            "meta": {"format": "docs-as-records", "kind": "answer"},
            "id": aid, "for": target,
            "title": f"{verdict} — {title or target}",
            "verdict": verdict, "chose": str(chose or "").strip(),
            "by": str(by).strip() or GIT_NAME,
            "at": date.today().isoformat(),
            "body": body,
            "relations": {"references": [target]},
        }
        _dump_record(doc, path)
        _sole_answer(target, path)
        now = _rev_now(target, "answer")
    return {"ok": True, "id": aid, "rev": now,
            "path": f"answers/{_slug(aid)}.yaml"}


IMAGE_EXT = {"image/png": ".png", "image/jpeg": ".jpg", "image/webp": ".webp",
             "image/gif": ".gif"}


def _rerender(script: str = "page.py") -> bool:
    """The corpus's own vendored renderer, in place.

    A row is a card only after a render, and its writer got a dim line and a
    sentence naming a command.

    `page.py render` never writes `atlas/`, so the reading view's own rebuild has
    to name `atlas.py`.
    """
    entry = EPIC / "bin" / script
    if not entry.exists():
        return False
    try:
        subprocess.run([sys.executable, str(entry), "render"], cwd=str(EPIC),
                       check=True, capture_output=True, timeout=600)
    except (subprocess.SubprocessError, OSError):
        return False
    return True


def _store_images(rid: str, images) -> tuple[list[str], str]:
    """Decode the pasted data URLs into `added/<rid>-<n>.<ext>`.

    `<n>` steps past every name already on disk, so an edit's pictures land beside
    the ones the row has instead of over them.
    """
    if isinstance(images, str):
        images = [images] if images else []
    rels, n = [], 1
    for image in images:
        head, _, data = str(image).partition(",")
        ext = IMAGE_EXT.get(head[5:].split(";")[0], ".png")
        try:
            raw = base64.b64decode(data, validate=True)
        except (ValueError, binascii.Error):
            return rels, "the pasted picture did not decode"
        while (CORPUS / "added" / f"{rid}-{n}{ext}").exists():
            n += 1
        rels.append(f"added/{rid}-{n}{ext}")
        (CORPUS / "added").mkdir(parents=True, exist_ok=True)
        (CORPUS / rels[-1]).write_bytes(raw)
    return rels, ""


def write_row(kind: str, status: str, group: str, body: str, images=()) -> dict:
    """A row for something the corpus holds no record for, from its pictures and a
    line about what is wrong with them.

    The margin note carries the same words, which is what hands the row to a sweep.
    """
    if not str(body).strip():
        return {"ok": False, "error": "a row with no words is a picture nobody can act on"}
    with _WRITE_LOCK:
        n = 1
        while (RECORD_DIR / f"new-{n}.yaml").exists():
            n += 1
        rid = f"new-{n}"
        rels, err = _store_images(rid, images)
        if err:
            return {"ok": False, "error": err}
        _dump_record({"meta": {"format": "docs-as-records", "kind": kind or "record"},
                      "id": rid, "title": f"Added by hand - {rid}",
                      "status": status or "open", "group": group or "Added by hand",
                      "tldr": " ".join(str(body).split()),
                      "evidence": rels},
                     RECORD_DIR / f"{rid}.yaml")
    note = write_note(rid, body)
    return {"ok": True, "id": rid, "rev": note.get("rev", ""),
            "path": f"records/{rid}.yaml", "rendered": _rerender()}


def edit_row(target: str, body: str, images=()) -> dict:
    """A hand-added row, said again: new words in place of its old ones, new pictures
    added to the ones it holds.

    Only `new-<n>` — a row this page itself wrote. Everything else in `records/` was
    poured, and the next pass would overwrite the edit anyway.
    """
    if not str(body).strip():
        return {"ok": False, "error": "a row with no words is a picture nobody can act on"}
    if not re.fullmatch(r"new-\d+", target):
        return {"ok": False, "error": f"{target} is not a hand-added row — "
                                      f"the margin note is where a poured row takes words"}
    path = RECORD_DIR / f"{target}.yaml"
    if not path.is_file():
        return {"ok": False, "error": f"no records/{target}.yaml to edit"}
    with _WRITE_LOCK:
        doc = _load_record(path)
        held = doc.get("evidence") or []
        if isinstance(held, str):
            held = [held]
        if any(not isinstance(e, str) for e in held):
            return {"ok": False, "error": f"{target} carries evidence this page cannot "
                                          f"rewrite — edit records/{target}.yaml by hand"}
        rels, err = _store_images(target, images)
        if err:
            return {"ok": False, "error": err}
        # `_dump_record` reads both meta keys straight, and a file edited by hand
        # since may be missing one.
        meta = doc.get("meta") or {}
        doc["meta"] = {"format": meta.get("format") or "docs-as-records",
                       "kind": meta.get("kind") or "record"}
        doc["tldr"] = " ".join(str(body).split())
        doc["evidence"] = list(held) + rels
        _dump_record(doc, path)
    note = write_note(target, body)
    return {"ok": True, "id": target, "rev": note.get("rev", ""),
            "path": f"records/{target}.yaml", "rendered": _rerender()}


def delete_row(target: str) -> dict:
    """A hand-added row taken back off: the record, its pictures, its note and
    its verdict.

    `+ Add row` writes a card and a pasted screenshot, and nothing on the board
    removed either, so a row added by a slip was permanent.
    """
    if not re.fullmatch(r"new-\d+", target):
        return {"ok": False, "error": f"{target} was poured, not added here — the next "
                                      f"pass owns it, and removing it changes nothing"}
    path = RECORD_DIR / f"{target}.yaml"
    if not path.is_file():
        return {"ok": False, "error": f"no records/{target}.yaml to remove"}
    with _WRITE_LOCK:
        held = _load_record(path).get("evidence") or []
        if isinstance(held, str):
            held = [held]
        # Only `added/<rid>-<n>`, which is where a pasted picture lands: a row may
        # cite a corpus asset that every other row cites too.
        pics = [e for e in held
                if isinstance(e, str) and e.startswith(f"added/{target}-")
                and (CORPUS / e).is_file()]
        for rel in pics:
            (CORPUS / rel).unlink()
        path.unlink()
        _sole_answer(target, None)
        note = NOTE_DIR / f"NOTE-{_slug(target)}.yaml"
        if note.exists():
            note.unlink()
    return {"ok": True, "removed": True, "pictures": len(pics),
            "path": f"records/{target}.yaml", "rendered": _rerender()}


# --------------------------------------------------------------------------- #
# server
# --------------------------------------------------------------------------- #
class Handler(BaseHTTPRequestHandler):
    server_version = "docs-as-records-page"

    def log_message(self, fmt, *args):
        pass  # quiet: this runs in a terminal somebody is reading

    def _send(self, code: int, body: bytes, ctype: str) -> None:
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        try:
            self.wfile.write(body)
        except (BrokenPipeError, ConnectionResetError):
            pass

    def _json(self, obj, code: int = 200) -> None:
        self._send(code, json.dumps(obj).encode("utf-8"), "application/json")

    def _notfound(self, path: str) -> None:
        """A dead link is a page somebody is looking at, so it names what is
        missing and carries the doors every other page here carries."""
        back = (f'<a href="{escape(HOME, quote=True)}">← every board</a>' if HOME else "")
        # `/` serves the board, so an unrendered corpus 404s here and this page's
        # own door went straight back to it.
        unbuilt = path == "/page/index.html"
        why = ("Nothing has rendered this corpus yet, so there is no board to open. "
               "<code>python3 bin/page.py render</code> in it builds one." if unbuilt else
               "A record's own page goes when the record does, so a bookmark can "
               "outlive one.")
        doors = ("" if unbuilt else '<a href="/page/index.html">← the board</a>') + back
        self._send(404, (
            "<!doctype html><html lang=en><meta charset=utf-8>"
            "<meta name=viewport content=\"width=device-width,initial-scale=1\">"
            f"<title>Nothing at that address — {escape(EPIC.name)}</title>"
            "<style>:root{color-scheme:light dark}"
            "body{margin:0;padding:3rem 1.25rem;font:1rem/1.6 -apple-system,"
            "BlinkMacSystemFont,\"Segoe UI\",system-ui,sans-serif}"
            "main{max-width:74ch}h1{font-size:1.5rem;margin:0 0 .5rem}"
            "p{margin:0 0 1rem}code{overflow-wrap:anywhere}"
            "a{display:inline-block;padding:.35rem .8rem;margin-right:.5rem;"
            "border:1px solid;border-radius:7px;text-decoration:none;"
            "color:light-dark(#1c5bd6,#79aaff)}</style>"
            "<main><h1>Nothing at that address</h1>"
            f"<p>This corpus holds no <code>{escape(path)}</code>. {why}</p>"
            + (f"<p>{doors}</p>" if doors else "") + "</main>"
        ).encode("utf-8"), "text/html; charset=utf-8")

    def do_GET(self) -> None:  # BaseHTTPRequestHandler names the verb handlers
        path = unquote(urlparse(self.path).path)
        if path == "/healthz":
            return self._json({"marker": HEALTH_MARKER, "epic": str(EPIC),
                               "corpus": str(CORPUS)})
        if path == "/state":
            return self._json(read_state())
        if path == "/sweep":
            return self._json(sweep())
        if path == "/find":
            # GET: it reads and writes nothing, so a reader can keep the address.
            qs = parse_qs(urlparse(self.path).query)
            return self._json(deep_find((qs.get("q") or [""])[0]))
        if path in ("/", "/index.html"):
            path = "/page/index.html"
        # Rooted at the board so the renderer's `../shots/x.png` resolves the same
        # here and over file://; the corpus is tried second, for a record's own evidence.
        rel = path.lstrip("/")
        target = (EPIC / rel).resolve()
        if not target.is_file() and CORPUS != EPIC:
            target = (CORPUS / rel).resolve()
        if not str(target).startswith((str(EPIC), str(CORPUS))) or not target.is_file():
            return self._notfound(path)
        self._send(200, target.read_bytes(),
                   MIME.get(target.suffix.lower(), "application/octet-stream"))

    def do_POST(self) -> None:  # BaseHTTPRequestHandler names the verb handlers
        path = urlparse(self.path).path
        try:
            length = int(self.headers.get("Content-Length") or 0)
            payload = json.loads(self.rfile.read(length) or b"{}")
        except (ValueError, json.JSONDecodeError) as exc:
            return self._json({"ok": False, "error": f"bad payload: {exc}"}, 400)
        # The tab noticed the corpus moved under it, and a plain reload re-serves
        # the same index.html nobody has rebuilt.
        if path in ("/rebuild", "/rebuild-atlas"):
            script = "atlas.py" if path == "/rebuild-atlas" else "page.py"
            ok = _rerender(script)
            return self._json({"ok": True} if ok else
                              {"ok": False, "error": f"the corpus's own bin/{script} "
                               "did not render — read its output in the terminal"}, 200 if ok else 500)
        # A new row names no target: it IS the record the rest of them address.
        if path == "/add-row":
            res = write_row(str(payload.get("kind") or ""), str(payload.get("status") or ""),
                            str(payload.get("group") or ""), str(payload.get("body") or ""),
                            payload.get("images") or [])
            return self._json(res, 200 if res.get("ok") else 400)
        target = str(payload.get("for") or "").strip()
        if not target:
            return self._json({"ok": False, "error": "no target record"}, 400)
        if path == "/delete-row":
            res = delete_row(target)
            return self._json(res, 200 if res.get("ok") else 400)
        if path == "/edit-row":
            res = edit_row(target, str(payload.get("body") or ""),
                           payload.get("images") or [])
            return self._json(res, 200 if res.get("ok") else 400)
        # A caller naming no rev writes blind, as `curl` and the static patch do.
        # Only a tab can say what it read.
        rev = payload.get("rev")
        rev = rev if isinstance(rev, str) else None
        if path == "/note":
            res = write_note(target, str(payload.get("body") or ""),
                             str(payload.get("by") or ""), rev)
            return self._json(res, 200 if res.get("ok") else 409)
        if path == "/unanswer":
            res = clear_answer(target, rev)
            return self._json(res, 200 if res.get("ok") else 409)
        if path == "/answer":
            res = write_answer(target, str(payload.get("verdict") or ""),
                               str(payload.get("by") or ""), str(payload.get("body") or ""),
                               str(payload.get("title") or ""), rev,
                               str(payload.get("chose") or ""))
            code = 200 if res.get("ok") else (409 if res.get("stale") else 400)
            return self._json(res, code)
        return self._json({"ok": False, "error": "no such endpoint"}, 404)


def _already_serving(port: int) -> str | None:
    """Our own server, on this port, for THIS corpus? Then reuse it. A second
    instance would corrupt nothing (every write re-reads the directory), but two
    tabs on two ports is a way to lose track of which one you typed in."""
    try:
        conn = http.client.HTTPConnection("127.0.0.1", port, timeout=0.4)
        conn.request("GET", "/healthz")
        body = json.loads(conn.getresponse().read())
    except Exception:
        return None
    if body.get("marker") == HEALTH_MARKER and body.get("epic") == str(EPIC):
        return f"http://127.0.0.1:{port}/page/index.html"
    return None


def _free_port(preferred: int) -> int:
    for port in [preferred, *range(preferred + 1, preferred + 40)]:
        with socket.socket() as s:
            # The server below sets it. Without it, a board restarted on the port
            # it just left walks to the next one and moves its address.
            s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            try:
                s.bind(("127.0.0.1", port))
                return port
            except OSError:
                continue
    raise SystemExit(f"no free port in {preferred}..{preferred + 40}")


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(
        description="Serve this corpus's decision page, with notes and answers "
                    "written straight into the working tree.")
    ap.add_argument("--port", type=int, default=8790)
    ap.add_argument("--no-open", action="store_true", help="serve, but do not open a browser")
    ap.add_argument("--home", default="", help="URL of the serve-all front page, if one launched this")
    args = ap.parse_args(argv)
    global HOME
    HOME = args.home

    index = PAGE_DIR / "index.html"
    if not index.is_file():
        sys.exit(f"no rendered page at {index} — run `docs-as-records page render` first")

    running = _already_serving(args.port)
    if running:
        print(f"already serving → {running}")
        if not args.no_open:
            webbrowser.open(running)
        return 0

    port = _free_port(args.port)
    url = f"http://127.0.0.1:{port}/page/index.html"
    httpd = ThreadingHTTPServer(("127.0.0.1", port), Handler)
    print(f"decision page → {url}")
    print(f"board         → {EPIC}")
    print(f"corpus        → {CORPUS}"
          + ("  (records/ resolves here, and so do your answers)" if CORPUS != EPIC else ""))
    print("notes autosave to notes/ · answers land in answers/ · nothing is committed")
    if not args.no_open:
        threading.Timer(0.3, lambda: webbrowser.open(url)).start()
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        print("\nstopped. What you typed is on disk — `git status` to see it.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
