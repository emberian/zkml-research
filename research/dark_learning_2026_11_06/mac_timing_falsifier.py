"""Falsifier for the MAC check's sigma timing (Astra scholar brick: MAC challenge timing). One custodian shifts
its share at an opening (it does not know alpha). Without sigma commitments it waits for the others' sigma_i and
opens -sum, so the check passes; with commit-then-open its opening no longer matches its commitment.

    python3 mac_timing_falsifier.py      # exits 1 unless legacy ACCEPTS and committed REFUSES
"""
import sys

import spdz

def run(commit):
    p = 2305843009212399617
    e = spdz.Engine(p, 3, spdz.Dealer(p, 3, 9), cheat=dict(party=1, at_open=0, delta=5, rush_sigma=1))
    a = e.prep("ta", lambda: 11)
    e.open(a, "x")                       # party 1 shifts its broadcast share by 5: the opening reads 16
    try:
        e.mac_check("t", commit_sigma=commit)
        return "ACCEPT"
    except spdz.Abort as ex:
        return f"REFUSED ({ex})"

def main():
    legacy, fixed = run(False), run(True)
    print("no sigma commitment (rushing party):", legacy)
    print("sigma commit-then-open             :", fixed)
    ok = legacy == "ACCEPT" and fixed.startswith("REFUSED")
    print("FALSIFIER", "PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
