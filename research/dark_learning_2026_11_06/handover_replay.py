"""The Python reference's check of one native rotation: python3 handover_replay.py PROFILE NATIVE_LEDGER HANDOVER.bin

The native ledger replica's records up to its first rotate record are copied into a fresh Python Ledger (its head,
from the records, as Ledger._replay; the steps themselves are proofwire.py replay's job). Then the rotation is
re-submitted with the handover proof bytes: Python's handover.verify_bytes must accept it, and the record Python
appends must equal the native one (epoch, custodians, roots, sha256 of the proof). Negative control: the same bytes
with one byte flipped at the middle must be refused. Prints ROTATION PASS or FAIL; exit 0 on PASS."""
import json, os, sys, tempfile, time

import proofwire as PW


def main():
    prof, native, proof = sys.argv[1:4]
    PW.set_profile(prof)
    p = PW.he_field()
    lines = open(native).read().splitlines()
    at = next(k for k, l in enumerate(lines) if json.loads(l)["kind"] == "rotate")
    want = json.loads(lines[at])
    model = json.loads(lines[0])["model"]
    blob = open(proof, "rb").read()
    wd = tempfile.mkdtemp(prefix="ho-replay-")

    def run(name, b):
        path = os.path.join(wd, name + ".ledger")
        open(path, "w").write("\n".join(lines[:at]) + "\n")
        lg = PW.Ledger(path, model)
        t = time.time()
        ok, why = lg.rotate(p, want["custodians"], want["roots"], b)
        return ok, why, (lg.recs[-1] if ok else None), time.time() - t

    ok, why, rec, secs = run("honest", blob)
    same = ok and rec == want
    print(f"rotation to epoch {want['epoch']}: {ok} {why}, record {'equal to' if same else 'DIFFERS from'} the native one ({secs:.0f}s, {len(blob)} bytes)", flush=True)
    bad = bytearray(blob)
    bad[len(bad) // 2] ^= 1
    nok, nwhy, _, _ = run("flipped", bytes(bad))
    print(f"one byte flipped: {'refused' if not nok else 'ACCEPTED'} ({nwhy})", flush=True)
    good = same and not nok
    print("ROTATION", "PASS" if good else "FAIL")
    sys.exit(0 if good else 1)


if __name__ == "__main__":
    main()
