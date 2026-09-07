#!/usr/bin/env python3
"""One-shot control and persistent keyless adapter around unchanged roles.propose.

The adapter keeps precisely the existing CAS inspection dictionary across
requests. Existing get/parse/validate/hash/transition bodies are unmodified.
The one-shot mode uses the same metering wrapper but discards its CAS on exit.
"""
import argparse
import contextlib
import copy
import io
import json
from pathlib import Path
import sys
import time
from types import SimpleNamespace

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE / "frozen_core"))
import common
import roles


def verify_snapshot():
    pins = common.read_json(HERE / "source_pins.json")
    for name, entry in pins["core"].items():
        common.require(common.sha((HERE / "frozen_core" / name).read_bytes()) == entry["sha256"], "frozenCoreChanged:" + name)


class Adapter:
    def __init__(self, config, cas):
        verify_snapshot()
        self.config = Path(config).resolve()
        cfg = common.read_json(self.config)
        common.exact_keys(cfg, ["crypto_binary", "crypto_binary_sha256", "genesis_path", "genesis_sha256", "command_log"], "publicHostConfigOnly")
        self.genesis = common.load_genesis(cfg)
        self.cas_root = Path(cas).resolve()
        self.stats = {"cas_get_calls": 0, "full_blob_sha256_calls": 0,
                      "full_blob_sha256_bytes": 0, "crypto_calls": {}, "requests": 0}
        self.active_hashes = []
        original_sha = common.sha

        def metered_sha(data):
            result = original_sha(data)
            # The first sha in unmodified CAS.get is its complete blob hash.
            # Binary hashes and metadata hashes later in the call are separate.
            if self.active_hashes and not self.active_hashes[-1]:
                self.stats["full_blob_sha256_calls"] += 1
                self.stats["full_blob_sha256_bytes"] += len(data)
                self.active_hashes[-1] = True
            return result

        common.sha = metered_sha
        outer = self

        class MeteredCrypto(common.Crypto):
            def run(self, command, private_output=False, **kwargs):
                counts = outer.stats["crypto_calls"]
                counts[command] = counts.get(command, 0) + 1
                return super().run(command, private_output=private_output, **kwargs)

        class MeteredCAS(common.CAS):
            def get(self, hexdigest, kind="ct"):
                outer.stats["cas_get_calls"] += 1
                outer.active_hashes.append(False)
                try:
                    path = super().get(hexdigest, kind)
                    common.require(outer.active_hashes[-1], "missingFullBlobHash")
                    return path
                finally:
                    outer.active_hashes.pop()

        self.cas = MeteredCAS(self.cas_root, self.genesis, MeteredCrypto(cfg, "host", cfg["command_log"]))

        def reuse_cas(root, genesis, crypto):
            common.require(Path(root).resolve() == self.cas_root, "fixedHostCAS")
            common.require(common.canonical(genesis) == common.canonical(self.genesis), "fixedHostGenesis")
            common.require(crypto.binary == self.cas.crypto.binary and crypto.expected == self.cas.crypto.expected
                           and crypto.role == self.cas.crypto.role and crypto.log == self.cas.crypto.log, "fixedHostCrypto")
            return self.cas

        # Replace only the constructor looked up by the original propose body.
        # No journal source bytes, validator, CAS.get or transition are replaced.
        roles.CAS = reuse_cas

    def propose(self, head, authorization, out):
        before = copy.deepcopy(self.stats)
        stdout = io.StringIO()
        start = time.perf_counter_ns()
        with contextlib.redirect_stdout(stdout):
            roles.propose(SimpleNamespace(config=self.config, cas=self.cas_root,
                head=Path(head), authorization=Path(authorization), out=Path(out)))
        elapsed = time.perf_counter_ns() - start
        self.stats["requests"] += 1
        delta = {k: self.stats[k] - before[k] for k in self.stats if k != "crypto_calls"}
        delta["crypto_calls"] = {k: n - before["crypto_calls"].get(k, 0) for k, n in self.stats["crypto_calls"].items()}
        return {"ok": True, "result": common.parse_json(stdout.getvalue()), "elapsed_ns": elapsed,
                "request_stats": delta, "cumulative_stats": self.stats,
                "inspection_cache_entries": len(self.cas.inspected)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=["once", "serve"])
    parser.add_argument("--config", required=True)
    parser.add_argument("--cas", required=True)
    parser.add_argument("--head")
    parser.add_argument("--authorization")
    parser.add_argument("--out")
    args = parser.parse_args()
    adapter = Adapter(args.config, args.cas)
    if args.mode == "once":
        reply = adapter.propose(args.head, args.authorization, args.out)
        print(common.canonical(reply).decode(), flush=True)
        return
    print(common.canonical({"ok": True, "ready": True}).decode(), flush=True)
    for raw in sys.stdin.buffer:
        try:
            common.require(len(raw) <= 2000000, "hostRequestSize")
            message = common.parse_json(raw)
            common.require(common.canonical(message) + b"\n" == raw, "hostRequestCanonical")
            common.exact_keys(message, ["head", "authorization", "out"], "hostRequestFields")
            reply = adapter.propose(**message)
        except Exception as error:
            reply = {"ok": False, "reason": str(error), "error_type": type(error).__name__}
        print(common.canonical(reply).decode(), flush=True)


if __name__ == "__main__":
    main()
