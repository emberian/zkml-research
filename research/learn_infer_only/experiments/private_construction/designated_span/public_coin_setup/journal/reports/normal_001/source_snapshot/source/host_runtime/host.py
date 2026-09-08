#!/usr/bin/env python3
"""Designated DDH one-shot/persistent keyless adapter around unchanged roles.propose.

The adapter keeps precisely the existing CAS inspection dictionary across
requests. Existing get/parse/validate/hash/transition bodies are unmodified.
The one-shot mode uses the same metering wrapper but discards its CAS on exit.
"""
import argparse
import contextlib
import copy
import hashlib
import io
import json
from pathlib import Path
import sys
import time
from types import SimpleNamespace

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
PINS_SHA256 = "17402dba697bd73da8aac4e519e6f7cbaeca25ecfce824d8f8cf45004e743bc7"


def verify_snapshot():
    # Check copied source bytes before importing any of them. The caller pins
    # this launcher; its constant in turn pins the source inventory.
    raw = (HERE / "source_pins.json").read_bytes()
    if hashlib.sha256(raw).hexdigest() != PINS_SHA256:
        raise ValueError("sourcePinsChanged")
    pins = json.loads(raw)
    for name, entry in pins["core"].items():
        if hashlib.sha256((HERE / "frozen_source" / name).read_bytes()).hexdigest() != entry["sha256"]:
            raise ValueError("frozenCoreChanged:" + name)
    return pins


PINS = verify_snapshot()
sys.path.insert(0, str(HERE / "frozen_source/journal"))
import common
import roles

class Adapter:
    def __init__(self, config, cas):
        verify_snapshot()
        self.config = Path(config).resolve()
        cfg = common.read_json(self.config)
        common.exact_keys(cfg, ["crypto_binary", "crypto_binary_sha256", "crypto_sources", "native_dependency",
                               "crypto_context", "crypto_context_sha256", "genesis_path", "genesis_sha256", "command_log"], "publicHostConfigOnly")
        self.fixed_config = common.canonical(cfg)
        self.genesis = common.load_genesis(cfg)
        common.require(cfg["crypto_sources"] == PINS["crypto_runtime"], "fixedCryptoRuntimeSources")
        common.require(cfg["crypto_sources"] == self.genesis["crypto_sources"] and
                       cfg["crypto_binary_sha256"] == self.genesis["crypto_binary_sha256"] and
                       common.canonical(cfg["native_dependency"]) == common.canonical(self.genesis["native_dependency"]), "fixedGenesisCryptoSources")
        common.require(cfg["crypto_context_sha256"] == self.genesis["context_id"] == self.genesis["key_id"] == self.genesis["public_key_sha256"], "fixedGenesisContext")
        context_path = Path(cfg["crypto_context"])
        common.require(common.sha(context_path.read_bytes()) == cfg["crypto_context_sha256"], "fixedContextBytes")
        validation_path = Path(cfg["genesis_path"]).parent / "context_validation.json"
        validation_raw = validation_path.read_bytes()
        common.require(common.sha(validation_raw) == self.genesis["context_validation_sha256"], "pinnedSetupValidationRecord")
        validation = common.parse_json(validation_raw)
        common.require(validation["validated"] is True and validation["context_id"] == self.genesis["context_id"] and
                       validation["source_sha256"] == cfg["crypto_sources"] and
                       validation["validation_mode"] == "full_subgroups_and_token_consistency", "trustedSetupValidationIdentity")
        # The digest/result are trusted setup configuration, not a standalone
        # cryptographic certificate that an arbitrary caller can mint.
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
                common.require(command in ["inspect", "host-learn", "host-infer"] and not private_output,
                               "publicHostCryptoCommandsOnly")
                common.require(not ({"sk", "vector"} & set(kwargs)), "publicHostInputsOnly")
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
            common.require(common.canonical(crypto.config) == self.fixed_config and
                           crypto.role == self.cas.crypto.role and crypto.log == self.cas.crypto.log, "fixedHostCrypto")
            return self.cas

        # Replace only the constructor looked up by the original propose body.
        # No journal source bytes, validator, CAS.get or transition are replaced.
        roles.CAS = reuse_cas

    def propose(self, head, authorization, out):
        verify_snapshot()
        common.require(common.canonical(common.read_json(self.config)) == self.fixed_config, "fixedHostConfig")
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
    print(common.canonical({"ok": True, "ready": True, "source_pins_sha256": PINS_SHA256,
                            "context_id": adapter.genesis["context_id"], "inspection_cache_entries": 0}).decode(), flush=True)
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
