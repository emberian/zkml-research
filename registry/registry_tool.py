#!/usr/bin/env python3
"""zkml weight-commitment registry tool.

Computes a publishable commitment to an open-weight checkpoint WITHOUT
downloading it to disk: HTTP Range requests against the safetensors shards,
incremental hashing of every byte as it streams past, nothing retained but
hasher state.

Subcommands
    commit  <repo_id>     build a manifest + top-level commitment
    verify  <manifest>    cheap spot-audit: re-fetch a random sample and check
    canon   <manifest>    print the exact canonical preimage bytes (for diffing)
    tamper  <manifest>    produce a deliberately corrupted manifest (the tooth)

The format, the canonicalization and what the commitment does and does not
bind are specified in MANIFEST-FORMAT.md, which is normative.  This file is
one implementation of it; a second implementer should be able to reproduce
byte-identical commitments from the document alone.

Dependencies: the Python standard library.  BLAKE3 is used if `--hash blake3`
is requested AND the `blake3` module is importable; otherwise SHA-256.  The
algorithm actually used is recorded inside the committed core, so a manifest
never has to be interpreted against an assumption.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import os
import random
import struct
import sys
import time
import urllib.error
import urllib.request

TOOL_VERSION = "0.1.0"
FORMAT_NAME = "zkml-weight-registry"
FORMAT_VERSION = 1

# Domain separation tag.  The commitment preimage is this literal followed by
# the canonical serialization of the core object.  ASCII, trailing newline
# included.  See MANIFEST-FORMAT.md section "Commitment".
DOMAIN_TAG = b"zkml-weight-registry/v1\n"

USER_AGENT = f"zkml-registry-tool/{TOOL_VERSION} (+https://github.com/emberian)"

# Top-level files that are fetched in full and bound by the commitment when
# present.  Behavior-relevant and tiny.  Anything not on this list is NOT
# bound -- see MANIFEST-FORMAT.md "What this does not bind".
AUX_ALLOWLIST = (
    "config.json",
    "generation_config.json",
    "tokenizer.json",
    "tokenizer_config.json",
    "special_tokens_map.json",
    "vocab.json",
    "merges.txt",
    "chat_template.jinja",
    "preprocessor_config.json",
    "processor_config.json",
    "model.safetensors.index.json",
)

DEFAULT_CHUNK = 8 << 20
RECHECK_SLICE = 4096

# safetensors dtype -> bytes per element.  Used only to cross-check that a
# header's shape and its byte range agree; an unrecognized dtype is reported
# as a note rather than guessed at.
DTYPE_BYTES = {
    "BOOL": 1, "U8": 1, "I8": 1, "F8_E5M2": 1, "F8_E4M3": 1, "F8_E8M0": 1,
    "I16": 2, "U16": 2, "F16": 2, "BF16": 2,
    "I32": 4, "U32": 4, "F32": 4,
    "I64": 8, "U64": 8, "F64": 8,
}


# --------------------------------------------------------------------------
# hashing
# --------------------------------------------------------------------------


def resolve_hash_algorithm(requested: str) -> str:
    """Return the algorithm name actually usable, honouring the request."""
    if requested == "blake3":
        try:
            import blake3  # noqa: F401
        except ImportError:
            raise SystemExit(
                "--hash blake3 requested but the `blake3` module is not "
                "importable.  Install it or use --hash sha256."
            )
        return "blake3"
    if requested not in ("sha256", "sha512"):
        raise SystemExit(f"unsupported hash algorithm: {requested}")
    return requested


def new_hasher(alg: str):
    if alg == "blake3":
        import blake3

        return blake3.blake3()
    return hashlib.new(alg)


def hash_bytes(alg: str, data: bytes) -> str:
    h = new_hasher(alg)
    h.update(data)
    return h.hexdigest()


# --------------------------------------------------------------------------
# canonicalization  (normative text lives in MANIFEST-FORMAT.md)
# --------------------------------------------------------------------------


def check_canonicalizable(obj, path="core") -> None:
    """Refuse anything whose canonical form is implementation-dependent.

    Floats are banned outright (formatting is not portable); object keys must
    be ASCII (so code-point ordering and UTF-16 code-unit ordering agree, and
    RFC 8785 implementations sort identically to Python's sort_keys).
    """
    if isinstance(obj, bool) or obj is None or isinstance(obj, int):
        return
    if isinstance(obj, str):
        return
    if isinstance(obj, float):
        raise ValueError(f"{path}: float values are not permitted in the core")
    if isinstance(obj, list):
        for i, v in enumerate(obj):
            check_canonicalizable(v, f"{path}[{i}]")
        return
    if isinstance(obj, dict):
        for k, v in obj.items():
            if not isinstance(k, str):
                raise ValueError(f"{path}: non-string key {k!r}")
            if not k.isascii():
                raise ValueError(f"{path}: non-ASCII key {k!r}")
            check_canonicalizable(v, f"{path}.{k}")
        return
    raise ValueError(f"{path}: value of type {type(obj).__name__} is not permitted")


def canonical_bytes(core: dict) -> bytes:
    """The canonical serialization of the core object.  Pure ASCII."""
    check_canonicalizable(core)
    text = json.dumps(
        core,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
        allow_nan=False,
    )
    return text.encode("ascii")


def load_manifest(path: str) -> dict:
    """Read a manifest, transparently gunzipping a `.json.gz`.

    The giant structure-only manifests are mostly repeated key names and hex,
    so they compress ~23x (Kimi-K3: 145 MB -> 6.4 MB).  Compression is a
    storage detail and never touches the commitment: the preimage is computed
    from the parsed `core`, not from the file bytes.
    """
    if path.endswith(".gz"):
        with gzip.open(path, "rt", encoding="utf-8") as f:
            return json.load(f)
    with open(path) as f:
        return json.load(f)


def write_manifest(path: str, manifest: dict) -> None:
    tmp = path + ".tmp"
    opener = (
        (lambda: gzip.open(tmp, "wt", encoding="utf-8", compresslevel=9))
        if path.endswith(".gz")
        else (lambda: open(tmp, "w"))
    )
    with opener() as f:
        json.dump(manifest, f, indent=1, sort_keys=True)
        f.write("\n")
    os.replace(tmp, path)


def commitment_preimage(core: dict) -> bytes:
    return DOMAIN_TAG + canonical_bytes(core)


def compute_commitment(core: dict) -> str:
    alg = core["hash_algorithm"]
    return hash_bytes(alg, commitment_preimage(core))


# --------------------------------------------------------------------------
# HTTP
# --------------------------------------------------------------------------


class _AuthStrippingRedirectHandler(urllib.request.HTTPRedirectHandler):
    """Drop the Authorization header when a redirect leaves huggingface.co.

    HF resolve URLs redirect to a pre-signed CDN URL; the bearer token is
    neither needed nor appropriate there.  Range headers ARE preserved by the
    stdlib handler, which is what makes ranged fetches survive the 307.
    """

    def redirect_request(self, req, fp, code, msg, headers, newurl):
        new = super().redirect_request(req, fp, code, msg, headers, newurl)
        if new is None:
            return None
        host = urllib.request.urlparse(newurl).hostname or ""
        if not (host == "huggingface.co" or host.endswith(".huggingface.co")):
            for k in list(new.headers):
                if k.lower() == "authorization":
                    del new.headers[k]
            new.unredirected_hdrs.pop("Authorization", None)
        return new


def load_token() -> str | None:
    tok = os.environ.get("HF_TOKEN") or os.environ.get("HUGGING_FACE_HUB_TOKEN")
    if tok:
        return tok.strip()
    path = os.path.expanduser("~/.cache/huggingface/token")
    if os.path.exists(path):
        with open(path) as f:
            t = f.read().strip()
        return t or None
    return None


class GatedRepo(Exception):
    """The repo cannot be read: gated, private, or absent.

    HF answers all three the same way for privacy reasons, so the tool does
    not claim to distinguish them -- it records the status code it got.
    """


class Fetcher:
    """Ranged HTTP reader with length checks, retry and resume."""

    def __init__(
        self,
        timeout: int = 120,
        retries: int = 8,
        quiet: bool = False,
        use_auth: bool = True,
    ):
        self.timeout = timeout
        self.retries = retries
        self.quiet = quiet
        self.token = load_token() if use_auth else None
        self.bytes_fetched = 0
        self.requests = 0
        self.opener = urllib.request.build_opener(_AuthStrippingRedirectHandler())

    def _open(self, url: str, rng=None):
        req = urllib.request.Request(url)
        req.add_header("User-Agent", USER_AGENT)
        if rng is not None:
            lo, hi = rng
            req.add_header("Range", f"bytes={lo}-" if hi is None else f"bytes={lo}-{hi}")
        if self.token:
            req.add_header("Authorization", "Bearer " + self.token)
        self.requests += 1
        try:
            return self.opener.open(req, timeout=self.timeout)
        except urllib.error.HTTPError as e:
            if e.code in (401, 403, 404, 410):
                # Permanent.  Retrying a 404 eight times with backoff is two
                # wasted minutes and a log that looks like a network problem.
                raise GatedRepo(
                    f"HTTP {e.code} for {url} -- not readable: gated, private, "
                    f"or absent (the Hub answers all three alike, so this tool "
                    f"records the code rather than guessing which)"
                ) from e
            raise

    def get(self, url: str, rng=None) -> bytes:
        """One request, whole body, length-checked against the Range asked."""
        last = None
        for attempt in range(self.retries):
            try:
                with self._open(url, rng) as r:
                    body = r.read()
                    declared = r.headers.get("Content-Length")
                if rng is not None and rng[1] is not None:
                    want = rng[1] - rng[0] + 1
                    if len(body) != want:
                        raise IOError(
                            f"range fetch returned {len(body)} bytes, wanted "
                            f"{want} (server may have ignored Range): {url}"
                        )
                elif declared is not None and len(body) != int(declared):
                    # unranged fetch (aux files): a short read must not be
                    # hashed as if it were the whole file
                    raise IOError(
                        f"body is {len(body)} bytes but Content-Length said "
                        f"{declared}: {url}"
                    )
                self.bytes_fetched += len(body)
                return body
            except GatedRepo:
                raise
            except Exception as e:  # noqa: BLE001 - retry everything else
                last = e
                self._backoff(attempt, e)
        raise IOError(f"giving up on {url}: {last}")

    def size(self, url: str) -> int:
        """Total file length, read out of the Content-Range of a 1-byte GET."""
        for attempt in range(self.retries):
            try:
                with self._open(url, (0, 0)) as r:
                    cr = r.headers.get("Content-Range")
                    body = r.read()
                self.bytes_fetched += len(body)
                if not cr or "/" not in cr:
                    raise IOError(f"no Content-Range for {url} (ranges unsupported?)")
                total = cr.rsplit("/", 1)[1]
                if total == "*":
                    raise IOError(f"server would not state total length: {url}")
                return int(total)
            except GatedRepo:
                raise
            except Exception as e:  # noqa: BLE001
                self._backoff(attempt, e)
        raise IOError(f"could not determine size of {url}")

    def stream(self, url: str, start: int, end: int, chunk: int = DEFAULT_CHUNK):
        """Yield the byte range [start, end] in order, resuming across drops."""
        pos = start
        stalls = 0
        while pos <= end:
            before = pos
            try:
                with self._open(url, (pos, end)) as r:
                    while pos <= end:
                        want = min(chunk, end - pos + 1)
                        b = r.read(want)
                        if not b:
                            break
                        self.bytes_fetched += len(b)
                        pos += len(b)
                        yield b
            except GatedRepo:
                raise
            except Exception as e:  # noqa: BLE001
                if pos > before:
                    stalls = 0
                stalls += 1
                if stalls > self.retries:
                    raise IOError(f"stream of {url} failed at byte {pos}: {e}") from e
                self._backoff(stalls - 1, e)
                continue
            if pos <= end:
                stalls = 0 if pos > before else stalls + 1
                if stalls > self.retries:
                    raise IOError(f"stream of {url} stalled at byte {pos}")
                self._backoff(stalls, "short stream")
        if pos != end + 1:
            raise IOError(f"stream of {url} ended at {pos}, expected {end + 1}")

    def _backoff(self, attempt: int, why) -> None:
        delay = min(30.0, 1.5 * (2**attempt))
        if not self.quiet:
            print(f"    retry in {delay:.1f}s after {why}", file=sys.stderr)
        time.sleep(delay)


# --------------------------------------------------------------------------
# HuggingFace repo model
# --------------------------------------------------------------------------


HF_HOST = "huggingface.co"


def hf_api(fetcher: Fetcher, repo: str, revision: str) -> dict:
    url = f"https://{HF_HOST}/api/models/{repo}/revision/{revision}?blobs=true"
    return json.loads(fetcher.get(url))


def hf_file_url(repo: str, revision: str, path: str) -> str:
    return f"https://{HF_HOST}/{repo}/resolve/{revision}/{path}"


def parse_safetensors_header(fetcher: Fetcher, url: str) -> tuple[int, bytes, dict]:
    """Two small ranged reads: the u64 length prefix, then the JSON header."""
    prefix = fetcher.get(url, (0, 7))
    (hlen,) = struct.unpack("<Q", prefix)
    if hlen <= 0 or hlen > (256 << 20):
        raise IOError(f"implausible safetensors header length {hlen} for {url}")
    raw = fetcher.get(url, (8, 8 + hlen - 1))
    hdr = json.loads(raw)
    return hlen, raw, hdr


def tensor_entries(hdr: dict) -> list[tuple[str, dict]]:
    return sorted(
        (k, v) for k, v in hdr.items() if k != "__metadata__"
    )


# --------------------------------------------------------------------------
# commit
# --------------------------------------------------------------------------


def build_manifest(
    repo: str,
    revision_ref: str,
    mode: str,
    alg: str,
    chunk: int,
    fetcher: Fetcher,
) -> dict:
    t0 = time.time()
    notes: list[str] = []

    info = hf_api(fetcher, repo, revision_ref)
    sha = info["sha"]
    if not (len(sha) == 40 and all(c in "0123456789abcdef" for c in sha)):
        raise SystemExit(f"unexpected revision sha from HF API: {sha!r}")
    siblings = [s["rfilename"] for s in info.get("siblings", [])]
    # HF's own storage metadata: for LFS-backed files the API reports the
    # sha256 of the file contents.  It is an INDEPENDENT oracle on a full
    # stream (and, for a repo we cannot afford to stream, the publisher's
    # unverified attestation).  It stays OUT of the committed core: it is
    # HF metadata, not a property of the bytes, and a storage migration that
    # stopped reporting it would make old manifests unreproducible.
    blob_meta = {}
    for s in info.get("siblings", []):
        rec = {"size": s.get("size")}
        lfs = s.get("lfs") or {}
        if lfs.get("sha256"):
            rec["lfs_sha256"] = lfs["sha256"]
        blob_meta[s["rfilename"]] = rec
    print(f"repo {repo} @ {sha} ({len(siblings)} files)", file=sys.stderr)

    # ---- aux files: fetched whole, always bound -------------------------
    aux = []
    for name in AUX_ALLOWLIST:
        if name not in siblings:
            continue
        blob = fetcher.get(hf_file_url(repo, sha, name))
        aux.append(
            {"path": name, "byte_len": len(blob), "hash": hash_bytes(alg, blob)}
        )
        print(f"  aux {name} ({len(blob)} B)", file=sys.stderr)
    aux.sort(key=lambda a: a["path"])

    # ---- shard set ------------------------------------------------------
    index_blob = None
    if "model.safetensors.index.json" in siblings:
        index_blob = fetcher.get(
            hf_file_url(repo, sha, "model.safetensors.index.json")
        )
        weight_map = json.loads(index_blob)["weight_map"]
        shard_paths = sorted(set(weight_map.values()))
        index_present = True
    elif "model.safetensors" in siblings:
        weight_map = None
        shard_paths = ["model.safetensors"]
        index_present = False
        notes.append(
            "repo has no model.safetensors.index.json; the single top-level "
            "model.safetensors is the whole shard set"
        )
    else:
        raise SystemExit(
            f"{repo}: no model.safetensors.index.json and no model.safetensors "
            f"at the repo root -- nothing this tool knows how to bind"
        )
    for p in shard_paths:
        if "/" in p:
            raise SystemExit(f"{repo}: index names a non-top-level shard {p!r}")

    # ---- headers --------------------------------------------------------
    shards = []
    tensors = []
    for path in shard_paths:
        url = hf_file_url(repo, sha, path)
        hlen, raw_header, hdr = parse_safetensors_header(fetcher, url)
        file_len = fetcher.size(url)
        api_size = (blob_meta.get(path) or {}).get("size")
        if api_size is not None and api_size != file_len:
            raise SystemExit(
                f"{path}: Content-Range says {file_len} bytes but the Hub API "
                f"says {api_size} -- refusing to commit to an ambiguous file"
            )
        data_start = 8 + hlen
        ents = tensor_entries(hdr)

        ivals = []
        unknown_dtypes = set()
        for name, ent in ents:
            begin, end = ent["data_offsets"]
            if not (0 <= begin <= end):
                raise SystemExit(f"{path}:{name}: bad data_offsets {begin},{end}")
            if data_start + end > file_len:
                raise SystemExit(
                    f"{path}:{name}: offsets run past EOF "
                    f"({data_start + end} > {file_len})"
                )
            # shape x dtype must account for exactly the claimed byte range
            elem = DTYPE_BYTES.get(ent["dtype"])
            if elem is None:
                unknown_dtypes.add(ent["dtype"])
            else:
                n_elem = 1
                for d in ent["shape"]:
                    n_elem *= d
                if n_elem * elem != end - begin:
                    raise SystemExit(
                        f"{path}:{name}: shape {ent['shape']} of {ent['dtype']} "
                        f"needs {n_elem * elem} bytes but the range is "
                        f"{end - begin} -- the header is inconsistent"
                    )
            ivals.append((begin, end, name))
            tensors.append(
                {
                    "name": name,
                    "shard": path,
                    "dtype": ent["dtype"],
                    "shape": list(ent["shape"]),
                    "offset_begin": begin,
                    "offset_end": end,
                    "byte_len": end - begin,
                }
            )
        ivals.sort()
        covered = 0
        prev_end = 0
        overlaps = 0
        for begin, end, _ in ivals:
            if begin < prev_end:
                overlaps += 1
            covered += end - begin
            prev_end = max(prev_end, end)
        if overlaps:
            notes.append(f"{path}: {overlaps} overlapping tensor byte ranges")
        if unknown_dtypes:
            notes.append(
                f"{path}: shape/byte-length cross-check skipped for unknown "
                f"dtype(s) {sorted(unknown_dtypes)}"
            )
        data_region = file_len - data_start

        shards.append(
            {
                "path": path,
                "byte_len": file_len,
                "header_len": hlen,
                "data_start": data_start,
                "header_hash": hash_bytes(alg, raw_header),
                "n_tensors": len(ents),
                "tensor_bytes": covered,
                "unclaimed_data_bytes": data_region - covered,
            }
        )
        print(
            f"  shard {path}: {file_len} B, header {hlen} B, "
            f"{len(ents)} tensors, {data_region - covered} B unclaimed",
            file=sys.stderr,
        )

    if weight_map is not None:
        header_names = {t["name"]: t["shard"] for t in tensors}
        disagree = [n for n, s in weight_map.items() if header_names.get(n) != s]
        missing = [n for n in header_names if n not in weight_map]
        if disagree:
            notes.append(
                f"index.json weight_map disagrees with shard headers for "
                f"{len(disagree)} tensors (e.g. {sorted(disagree)[:3]})"
            )
        if missing:
            notes.append(
                f"{len(missing)} tensors present in shard headers but absent "
                f"from index.json weight_map (e.g. {sorted(missing)[:3]})"
            )

    tensors.sort(key=lambda t: t["name"])
    dupes = [
        tensors[i]["name"]
        for i in range(1, len(tensors))
        if tensors[i]["name"] == tensors[i - 1]["name"]
    ]
    if dupes:
        raise SystemExit(f"{repo}: duplicate tensor names across shards: {dupes[:5]}")

    rechecks = []
    lfs_crosscheck = []

    # ---- full mode: stream every shard byte, hash as it passes ----------
    if mode == "full":
        by_shard: dict[str, list[dict]] = {}
        for t in tensors:
            by_shard.setdefault(t["shard"], []).append(t)
        rng = random.Random(0xC0FFEE)
        for sh in shards:
            path = sh["path"]
            url = hf_file_url(repo, sha, path)
            file_len = sh["byte_len"]
            ds = sh["data_start"]
            ivals = sorted(
                (ds + t["offset_begin"], ds + t["offset_end"], t)
                for t in by_shard.get(path, [])
            )
            hashers = [new_hasher(alg) for _ in ivals]
            consumed = [0] * len(ivals)
            file_hasher = new_hasher(alg)

            # one interior slice, remembered while streaming, re-fetched after
            slice_lo = (
                rng.randrange(ds, max(ds + 1, file_len - RECHECK_SLICE))
                if file_len - ds > RECHECK_SLICE
                else ds
            )
            slice_hi = min(slice_lo + RECHECK_SLICE, file_len) - 1
            slice_buf = bytearray()

            head = 0
            pos = 0
            t_start = time.time()
            last_report = t_start
            for buf in fetcher.stream(url, 0, file_len - 1, chunk):
                file_hasher.update(buf)
                lo, hi = pos, pos + len(buf)
                if lo <= slice_hi and hi > slice_lo:
                    a = max(slice_lo, lo)
                    b = min(slice_hi + 1, hi)
                    slice_buf.extend(buf[a - lo : b - lo])
                while head < len(ivals) and ivals[head][1] <= lo:
                    head += 1
                j = head
                while j < len(ivals) and ivals[j][0] < hi:
                    tb, te, _ = ivals[j]
                    a = max(tb, lo)
                    b = min(te, hi)
                    if b > a:
                        hashers[j].update(buf[a - lo : b - lo])
                        consumed[j] += b - a
                    j += 1
                pos = hi
                now = time.time()
                if now - last_report > 30:
                    el = now - t_start
                    print(
                        f"    {path}: {pos / 1e9:.2f}/{file_len / 1e9:.2f} GB "
                        f"({pos / el / 1e6:.1f} MB/s)",
                        file=sys.stderr,
                    )
                    last_report = now
            if pos != file_len:
                raise IOError(f"{path}: streamed {pos} bytes, expected {file_len}")
            for j, (tb, te, t) in enumerate(ivals):
                if consumed[j] != te - tb:
                    raise IOError(
                        f"{path}:{t['name']}: hashed {consumed[j]} bytes, "
                        f"expected {te - tb}"
                    )
                t["hash"] = hashers[j].hexdigest()
            sh["file_hash"] = file_hasher.hexdigest()

            # independent oracle: HF's LFS oid is the sha256 of the file
            lfs = (blob_meta.get(path) or {}).get("lfs_sha256")
            if lfs and alg == "sha256":
                match = lfs == sh["file_hash"]
                lfs_crosscheck.append(
                    {"shard": path, "hub_lfs_sha256": lfs, "match": match}
                )
                if not match:
                    raise IOError(
                        f"{path}: streamed bytes hash to {sh['file_hash']} but "
                        f"the Hub reports LFS sha256 {lfs} -- the transfer or "
                        f"the repo disagrees with itself"
                    )
                print(f"  hub LFS sha256 agrees for {path}", file=sys.stderr)
            elif lfs:
                lfs_crosscheck.append(
                    {
                        "shard": path,
                        "hub_lfs_sha256": lfs,
                        "match": None,
                        "note": f"not comparable: manifest uses {alg}",
                    }
                )

            # integrity discipline: re-fetch one interior slice, compare
            again = fetcher.get(url, (slice_lo, slice_hi))
            ok = bytes(slice_buf) == again
            rechecks.append(
                {
                    "shard": path,
                    "offset": slice_lo,
                    "len": slice_hi - slice_lo + 1,
                    "match": ok,
                }
            )
            if not ok:
                raise IOError(
                    f"{path}: interior re-fetch at {slice_lo} disagrees with the "
                    f"streamed bytes -- the transfer is not reproducible"
                )
            el = time.time() - t_start
            print(
                f"  streamed {path}: {file_len / 1e9:.2f} GB in {el / 60:.1f} min "
                f"({file_len / el / 1e6:.1f} MB/s), interior recheck OK",
                file=sys.stderr,
            )
    else:
        # structure mode binds the header bytes, so shapes/dtypes/offsets and
        # __metadata__ are all bound; the weight payload is not.
        for sh in shards:
            url = hf_file_url(repo, sha, sh["path"])
            raw = fetcher.get(url, (8, 8 + sh["header_len"] - 1))
            again = hash_bytes(alg, raw)
            rechecks.append(
                {
                    "shard": sh["path"],
                    "offset": 8,
                    "len": sh["header_len"],
                    "match": again == sh["header_hash"],
                }
            )
            if again != sh["header_hash"]:
                raise IOError(f"{sh['path']}: header re-fetch disagrees")
            lfs = (blob_meta.get(sh["path"]) or {}).get("lfs_sha256")
            if lfs:
                lfs_crosscheck.append(
                    {
                        "shard": sh["path"],
                        "hub_lfs_sha256": lfs,
                        "match": None,
                        "note": "PUBLISHER ATTESTATION, NOT VERIFIED BY US -- "
                        "the weight bytes were never streamed; this is the "
                        "Hub's own metadata, recorded so a future full run "
                        "can be checked against it",
                    }
                )

    core = {
        "format": FORMAT_NAME,
        "format_version": FORMAT_VERSION,
        "hash_algorithm": alg,
        "coverage": "full" if mode == "full" else "structure-only",
        "source": {
            "host": HF_HOST,
            "repo_id": repo,
            "revision": sha,
            "index_present": index_present,
        },
        "aux_files": aux,
        "shards": shards,
        "tensors": tensors,
    }
    commitment = compute_commitment(core)

    total_tensor_bytes = sum(t["byte_len"] for t in tensors)
    total_shard_bytes = sum(s["byte_len"] for s in shards)
    elapsed = time.time() - t0
    manifest = {
        "format": FORMAT_NAME,
        "commitment": commitment,
        "core": core,
        "annotations": {
            "tool_version": TOOL_VERSION,
            "generated_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "wall_seconds": round(elapsed, 1),
            "bytes_fetched": fetcher.bytes_fetched,
            "http_requests": fetcher.requests,
            "auth_used": fetcher.token is not None,
            "n_tensors": len(tensors),
            "n_shards": len(shards),
            "tensor_bytes": total_tensor_bytes,
            "shard_bytes": total_shard_bytes,
            "interior_rechecks": rechecks,
            "hub_lfs_crosscheck": lfs_crosscheck,
            "notes": notes,
        },
    }
    return manifest


def cmd_commit(args) -> int:
    alg = resolve_hash_algorithm(args.hash)
    fetcher = Fetcher(timeout=args.timeout, use_auth=not args.no_auth)
    try:
        manifest = build_manifest(
            args.repo, args.revision, args.mode, alg, args.chunk, fetcher
        )
    except GatedRepo as e:
        print(f"GATED/UNAVAILABLE {args.repo}: {e}", file=sys.stderr)
        return 2
    core = manifest["core"]
    out = args.out
    if out is None:
        slug = args.repo.replace("/", "__")
        rev = core["source"]["revision"][:12]
        cov = "full" if core["coverage"] == "full" else "structure"
        out = os.path.join(
            os.path.dirname(os.path.abspath(__file__)),
            "manifests",
            f"{slug}.{rev}.{cov}.json",
        )
    os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
    write_manifest(out, manifest)
    ann = manifest["annotations"]
    print(f"\ncommitment  {manifest['commitment']}")
    print(f"algorithm   {core['hash_algorithm']}")
    print(f"coverage    {core['coverage']}")
    print(f"repo        {core['source']['repo_id']} @ {core['source']['revision']}")
    print(f"tensors     {ann['n_tensors']} in {ann['n_shards']} shards")
    print(f"tensor B    {ann['tensor_bytes']}")
    print(f"fetched     {ann['bytes_fetched']} B in {ann['http_requests']} requests")
    print(f"wall        {ann['wall_seconds']} s")
    for n in ann["notes"]:
        print(f"note        {n}")
    print(f"written     {out}")
    return 0


# --------------------------------------------------------------------------
# verify -- the cheap spot audit
# --------------------------------------------------------------------------


def redrive_shard(hdr: dict, sh: dict, all_tensors: list[dict]) -> list[str]:
    """Recompute a shard's structural claims from its live header bytes.

    Returns a list of disagreements with what the manifest recorded.  This is
    the check that stops a producer from committing to tensor byte ranges the
    header never named -- header_hash proves the header is authentic, not that
    the manifest describes it.
    """
    problems = []
    ents = dict(tensor_entries(hdr))
    recorded = {t["name"]: t for t in all_tensors if t["shard"] == sh["path"]}

    if sh["data_start"] != 8 + sh["header_len"]:
        problems.append(
            f"data_start {sh['data_start']} != 8 + header_len {sh['header_len']}"
        )
    if sh["n_tensors"] != len(ents):
        problems.append(f"n_tensors {sh['n_tensors']} but header has {len(ents)}")
    only_manifest = sorted(set(recorded) - set(ents))
    only_header = sorted(set(ents) - set(recorded))
    if only_manifest:
        problems.append(f"tensors in manifest but not header: {only_manifest[:3]}")
    if only_header:
        problems.append(f"tensors in header but not manifest: {only_header[:3]}")

    covered = 0
    for name, ent in ents.items():
        begin, end = ent["data_offsets"]
        covered += end - begin
        t = recorded.get(name)
        if t is None:
            continue
        if [t["offset_begin"], t["offset_end"]] != [begin, end]:
            problems.append(
                f"{name}: manifest range [{t['offset_begin']},{t['offset_end']}) "
                f"but header says [{begin},{end})"
            )
        if t["byte_len"] != end - begin:
            problems.append(f"{name}: byte_len {t['byte_len']} != {end - begin}")
        if t["dtype"] != ent["dtype"]:
            problems.append(f"{name}: dtype {t['dtype']} != {ent['dtype']}")
        if list(t["shape"]) != list(ent["shape"]):
            problems.append(f"{name}: shape {t['shape']} != {ent['shape']}")
    if sh["tensor_bytes"] != covered:
        problems.append(f"tensor_bytes {sh['tensor_bytes']} != {covered} from header")
    if sh["unclaimed_data_bytes"] != sh["byte_len"] - sh["data_start"] - covered:
        problems.append("unclaimed_data_bytes disagrees with the header")
    return problems


def cmd_verify(args) -> int:
    manifest = load_manifest(args.manifest)
    core = manifest["core"]
    alg = core["hash_algorithm"]
    repo = core["source"]["repo_id"]
    rev = core["source"]["revision"]
    failures: list[str] = []
    checked = 0

    print(f"verifying {args.manifest}")
    print(f"  repo {repo} @ {rev}  coverage={core['coverage']}  hash={alg}")

    # 1. the commitment must recompute from the core.  This is what makes
    #    every subsequent check meaningful: it binds the claims we test.
    recomputed = compute_commitment(core)
    if recomputed != manifest.get("commitment"):
        failures.append(
            f"commitment mismatch: file says {manifest.get('commitment')}, "
            f"core hashes to {recomputed}"
        )
        print(f"  FAIL commitment: {manifest.get('commitment')} != {recomputed}")
    else:
        print(f"  ok   commitment recomputes: {recomputed}")
    checked += 1

    fetcher = Fetcher(timeout=args.timeout, use_auth=not args.no_auth)
    rng = random.Random(args.seed)

    try:
        # 2. aux files in full -- tiny, so always all of them
        for a in core["aux_files"]:
            blob = fetcher.get(hf_file_url(repo, rev, a["path"]))
            got = hash_bytes(alg, blob)
            checked += 1
            if len(blob) != a["byte_len"] or got != a["hash"]:
                failures.append(f"aux {a['path']}: hash/length mismatch")
                print(f"  FAIL aux {a['path']}")
            else:
                print(f"  ok   aux {a['path']} ({a['byte_len']} B)")

        # 3. a sample of shard headers -- binds structure claims
        shards = core["shards"]
        n_sh = len(shards) if args.all_shards else min(args.shard_sample, len(shards))
        sample_sh = rng.sample(shards, n_sh)
        for sh in sorted(sample_sh, key=lambda s: s["path"]):
            url = hf_file_url(repo, rev, sh["path"])
            raw = fetcher.get(url, (8, 8 + sh["header_len"] - 1))
            got = hash_bytes(alg, raw)
            checked += 1
            if got != sh["header_hash"]:
                failures.append(f"shard {sh['path']}: header hash mismatch")
                print(f"  FAIL header {sh['path']}")
                continue
            size = fetcher.size(url)
            checked += 1
            if size != sh["byte_len"]:
                failures.append(
                    f"shard {sh['path']}: length {size} != recorded {sh['byte_len']}"
                )
                print(f"  FAIL length {sh['path']}")
                continue

            # Re-derive the structural claims from the header bytes we just
            # fetched, rather than trusting that the producer transcribed them
            # honestly.  header_hash alone would not catch a manifest whose
            # tensor records point at byte ranges the header never named.
            checked += 1
            problems = redrive_shard(json.loads(raw), sh, core["tensors"])
            if problems:
                for pr in problems:
                    failures.append(f"shard {sh['path']}: {pr}")
                    print(f"  FAIL structure {sh['path']}: {pr}")
            else:
                print(f"  ok   header+length+structure {sh['path']}")

        # 3b. free full-file cross-check: the Hub's own LFS sha256 for every
        #     shard, against the file_hash we committed to.  One API call, no
        #     payload transfer.  A missing oid is REPORTED, never silently
        #     treated as a pass.
        if core["coverage"] == "full" and alg == "sha256":
            info = hf_api(fetcher, repo, rev)
            meta = {
                s["rfilename"]: (s.get("lfs") or {}).get("sha256")
                for s in info.get("siblings", [])
            }
            n_ok = n_absent = 0
            for sh in core["shards"]:
                oid = meta.get(sh["path"])
                if not oid:
                    n_absent += 1
                    print(f"  --   no Hub LFS oid reported for {sh['path']}")
                    continue
                checked += 1
                if oid != sh.get("file_hash"):
                    failures.append(
                        f"shard {sh['path']}: Hub LFS sha256 {oid} != committed "
                        f"file_hash {sh.get('file_hash')}"
                    )
                    print(f"  FAIL hub oid {sh['path']}")
                else:
                    n_ok += 1
            if n_ok:
                print(
                    f"  ok   hub LFS sha256 agrees on {n_ok}/{len(core['shards'])} "
                    f"whole shards (publisher metadata, same trust domain)"
                )
            if n_absent:
                print(f"  note {n_absent} shard(s) had no Hub oid to compare")

        # 4. a random sample of tensor byte ranges -- the payload audit
        tensors = core["tensors"]
        if core["coverage"] != "full":
            print(
                "  --   structure-only manifest: no tensor payload hashes to "
                "check (this manifest never claimed to bind weight bytes)"
            )
        elif args.tensors:
            names = set(args.tensors.split(","))
            picks = [t for t in tensors if t["name"] in names]
            missing = names - {t["name"] for t in picks}
            if missing:
                failures.append(f"--tensors named absent tensors: {sorted(missing)}")
                print(f"  FAIL no such tensor(s): {sorted(missing)}")
        else:
            n = min(args.sample, len(tensors))
            picks = rng.sample(tensors, n)
        if core["coverage"] == "full":
            shard_by_path = {s["path"]: s for s in core["shards"]}
            for t in sorted(picks, key=lambda t: t["name"]):
                sh = shard_by_path[t["shard"]]
                lo = sh["data_start"] + t["offset_begin"]
                hi = sh["data_start"] + t["offset_end"] - 1
                if hi < lo:
                    print(f"  --   {t['name']}: zero-length tensor, nothing to fetch")
                    continue
                h = new_hasher(alg)
                got_len = 0
                for buf in fetcher.stream(
                    hf_file_url(repo, rev, t["shard"]), lo, hi, args.chunk
                ):
                    h.update(buf)
                    got_len += len(buf)
                checked += 1
                if got_len != t["byte_len"] or h.hexdigest() != t["hash"]:
                    failures.append(
                        f"tensor {t['name']}: payload hash mismatch "
                        f"({got_len} B fetched)"
                    )
                    print(f"  FAIL tensor {t['name']} ({t['byte_len']} B)")
                else:
                    print(f"  ok   tensor {t['name']} ({t['byte_len']} B)")
    except GatedRepo as e:
        failures.append(f"repo became unavailable: {e}")
        print(f"  FAIL {e}")

    n_t = len(core["tensors"])
    print()
    print(f"  checks run     {checked}")
    print(f"  bytes fetched  {fetcher.bytes_fetched}")
    if core["coverage"] == "full" and not args.tensors and n_t:
        k = min(args.sample, n_t)
        print(
            f"  audit game     sampled {k}/{n_t} tensors uniformly without "
            f"replacement; an adversary who altered a fraction f of tensors "
            f"evades with probability about (1-f)^{k} "
            f"(f=0.01 -> {(0.99**k):.3f}, f=0.10 -> {(0.90**k):.3f})"
        )
    if failures:
        print(f"\nVERIFY FAILED: {len(failures)} problem(s)")
        for f_ in failures:
            print(f"  - {f_}")
        return 1
    print("\nVERIFY PASSED")
    return 0


# --------------------------------------------------------------------------
# canon / tamper
# --------------------------------------------------------------------------


def cmd_canon(args) -> int:
    manifest = load_manifest(args.manifest)
    data = commitment_preimage(manifest["core"])
    if args.digest_only:
        print(compute_commitment(manifest["core"]))
    else:
        sys.stdout.buffer.write(data)
    return 0


def cmd_tamper(args) -> int:
    """Build a deliberately corrupted manifest.  The falsifier.

    Every mode asserts that it actually changed something -- a mutation that
    silently becomes a no-op is how a tooth stops biting.
    """
    manifest = load_manifest(args.manifest)
    before = json.dumps(manifest, sort_keys=True)
    core = manifest["core"]
    mode = args.mode
    what = ""

    def flip(hexstr: str) -> str:
        c = hexstr[-1]
        return hexstr[:-1] + ("0" if c != "0" else "1")

    if mode == "tensor-hash":
        cands = [t for t in core["tensors"] if "hash" in t and t["byte_len"] > 0]
        if not cands:
            raise SystemExit("no hashed tensors to corrupt (structure-only manifest?)")
        if args.tensor_name:
            named = [t for t in cands if t["name"] == args.tensor_name]
            if not named:
                raise SystemExit(f"no hashed tensor named {args.tensor_name!r}")
            t = named[0]
        else:
            t = cands[args.index % len(cands)]
        t["hash"] = flip(t["hash"])
        what = f"tensor {t['name']} hash flipped"
        # keep the commitment consistent so the failure lands on the PAYLOAD
        # check, not on the commitment check -- this is the interesting tooth
        manifest["commitment"] = compute_commitment(core)
        print(f"tampered tensor: {t['name']}")
    elif mode == "aux-hash":
        a = core["aux_files"][args.index % len(core["aux_files"])]
        a["hash"] = flip(a["hash"])
        what = f"aux {a['path']} hash flipped"
        manifest["commitment"] = compute_commitment(core)
    elif mode == "commitment":
        manifest["commitment"] = flip(manifest["commitment"])
        what = "top-level commitment flipped"
    elif mode == "byte-len":
        t = core["tensors"][args.index % len(core["tensors"])]
        t["byte_len"] = t["byte_len"] + 1
        what = f"tensor {t['name']} byte_len +1 (core edited, commitment stale)"
    elif mode == "file-hash":
        cands = [s for s in core["shards"] if "file_hash" in s]
        if not cands:
            raise SystemExit("no shard file hashes to corrupt (structure-only?)")
        sh = cands[args.index % len(cands)]
        sh["file_hash"] = flip(sh["file_hash"])
        what = f"shard {sh['path']} file_hash flipped"
        manifest["commitment"] = compute_commitment(core)
    elif mode == "offsets":
        # A manifest that binds hashes of byte ranges the header never named.
        # Commitment stays consistent, header_hash stays correct: only the
        # verifier's re-derivation of structure from the header can see it.
        t = core["tensors"][args.index % len(core["tensors"])]
        t["offset_begin"] += 8
        t["offset_end"] += 8
        what = f"tensor {t['name']} byte range shifted by 8"
        manifest["commitment"] = compute_commitment(core)
    elif mode == "header-hash":
        sh = core["shards"][args.index % len(core["shards"])]
        sh["header_hash"] = flip(sh["header_hash"])
        what = f"shard {sh['path']} header hash flipped"
        manifest["commitment"] = compute_commitment(core)
    else:
        raise SystemExit(f"unknown tamper mode {mode}")

    after = json.dumps(manifest, sort_keys=True)
    if after == before:
        raise SystemExit(
            f"tamper mode {mode} produced an IDENTICAL manifest -- the "
            f"falsifier is a no-op and would leave the gate green"
        )
    write_manifest(args.out, manifest)
    print(f"tampered ({mode}): {what}")
    print(f"written {args.out}")
    return 0


# --------------------------------------------------------------------------


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = p.add_subparsers(dest="cmd", required=True)

    c = sub.add_parser("commit", help="build a manifest for a HF repo")
    c.add_argument("repo", help="HuggingFace repo id, e.g. openai/gpt-oss-20b")
    c.add_argument("--revision", default="main", help="branch/tag/sha; pinned to sha")
    c.add_argument("--mode", choices=("full", "structure"), default="full")
    c.add_argument("--hash", default="sha256", choices=("sha256", "sha512", "blake3"))
    c.add_argument("--chunk", type=int, default=DEFAULT_CHUNK)
    c.add_argument("--timeout", type=int, default=120)
    c.add_argument(
        "--no-auth",
        action="store_true",
        help="ignore any HF token: fetch as an anonymous stranger would",
    )
    c.add_argument("--out", default=None)
    c.set_defaults(func=cmd_commit)

    v = sub.add_parser("verify", help="spot-audit a manifest against the live repo")
    v.add_argument("manifest")
    v.add_argument("--sample", type=int, default=8, help="tensors to re-fetch")
    v.add_argument("--shard-sample", type=int, default=4, help="shard headers")
    v.add_argument("--all-shards", action="store_true")
    v.add_argument("--tensors", default=None, help="comma-separated names to force")
    v.add_argument("--seed", type=int, default=None)
    v.add_argument("--chunk", type=int, default=DEFAULT_CHUNK)
    v.add_argument("--timeout", type=int, default=120)
    v.add_argument("--no-auth", action="store_true")
    v.set_defaults(func=cmd_verify)

    n = sub.add_parser("canon", help="emit the exact commitment preimage")
    n.add_argument("manifest")
    n.add_argument("--digest-only", action="store_true")
    n.set_defaults(func=cmd_canon)

    t = sub.add_parser("tamper", help="produce a corrupted manifest (the tooth)")
    t.add_argument("manifest")
    t.add_argument("--out", required=True)
    t.add_argument(
        "--mode",
        default="tensor-hash",
        choices=(
            "tensor-hash",
            "aux-hash",
            "commitment",
            "byte-len",
            "header-hash",
            "offsets",
            "file-hash",
        ),
    )
    t.add_argument("--index", type=int, default=0)
    t.add_argument("--tensor-name", default=None, help="tensor-hash mode: pick by name")
    t.set_defaults(func=cmd_tamper)

    args = p.parse_args()
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
