"""run.py's XT redo (notes/dark-learning-gen6/xtrunc.md), driven with the boxes simulated: every custodian exits 5 at
step 1; `drive` waits for step 1's fresh preprocessing (it appears after a few polls), resumes step 1 ALONE on it
(--resume --steps 1 --tapes <xt_redo_tapes>, owner included), then resumes the steps left on the normal pattern, and
ends the run. A second scenario without xt_redo_tapes in the config makes `redo` refuse by name (it never guesses a
tape: preprocessing is single use). The real custodians' side of the same sequence (exit 5, the redo resume, the
next resume, equal to the twin) is darkstep tests/serve_xt.rs exit_5_then_resume_on_a_fresh_step_tape_equals_the_twin.

    python3 native/deploy/test_run_redo.py
"""
import json, os, re, sys, tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import run as R


def scenario(with_redo_cfg=True):
    out = tempfile.mkdtemp(prefix="run-redo-")
    seats = []
    for i in range(3):
        s = {"host": f"box{i}", "root": "/r", "bin": "/b", "addr": f"10.0.0.{i}:1", "tapes": f"/c/rec-c{{c}}-P{i}/step-{{j}}/tape_{i}.bin",
             "owner_msgs": f"/c/rec-c{{c}}-P{i}/step-{{j}}/owner-msg-P{i}.bin"}
        if with_redo_cfg:
            s["xt_redo_tapes"] = f"/c/rec-xs{{k}}-{{r}}-P{i}/step-0/tape_{i}.bin"
            s["xt_redo_owner_msgs"] = f"/c/rec-xs{{k}}-{{r}}-P{i}/step-0/owner-msg-P{i}.bin"
        seats.append(s)
    cfg = {"name": "t", "out": out, "prof": [16384, 4, 175, 64], "t": 7, "gate": 309, "program": "gen6", "steps": 3,
           "flags": ["--rs", "--xt", "--chunk-steps", "2"], "seats": seats,
           "owner": {"host": "boxo", "root": "/r", "bin": "/b", "addr": "10.0.0.9:1", "test_public": "/x"},
           "drive_poll_s": 0, "disk_poll_s": 0}
    files = set()
    serve = {i: {"exit": 5, "next_step": 1} for i in range(3)}
    launches = []
    polls = {"n": 0}

    def sh(host, cmd, check=True, capture=True):
        m = re.search(r"cat (\S+)/D/serve_P(\d)\.json", cmd)
        if m:
            return json.dumps(serve[int(m.group(2))])
        if "handover_P" in cmd or "release_P" in cmd:
            return "null"
        if cmd.startswith("test -f /c/"):
            return "y" if all(t in files for t in re.findall(r"test -f (\S+)", cmd)) else "n"
        if "serve0.pid && echo y" in cmd:
            return "y"
        return ""

    def launch(c, seats_only=False, with_new=True):
        a = dict(steps=c["steps"], resume="--resume" in c["flags"], tapes=[s["tapes"] for s in c["seats"]],
                 owner_msgs=[s["owner_msgs"] for s in c["seats"]], tape=[s.get("tape") for s in c["seats"]])
        launches.append(a)
        # the simulated custodians: the redo segment runs step 1, the next segment runs the rest
        nxt = serve[0]["next_step"] + c["steps"]
        for i in range(3):
            serve[i] = {"exit": 0, "next_step": nxt}

    def sleep(_):
        polls["n"] += 1
        if polls["n"] == 3:
            # the fresh one-step chunk for step 1 lands on every seat (prep writes chunk-P<I>.json last)
            for i in range(3):
                d = f"/c/rec-xs1-0-P{i}"
                files.update({f"{d}/step-0/tape_{i}.bin", f"{d}/step-0/owner-msg-P{i}.bin", f"{d}/chunk-P{i}.json"})

    R.sh, R.launch, R.alive, R.collect, R.stop, R.start_nightly = sh, launch, (lambda *a: False), (lambda c: None), (lambda c: None), (lambda c: None)
    R.time.sleep = sleep
    return cfg, launches, polls, serve, out


def main():
    cfg, launches, polls, serve, out = scenario()
    R.drive(cfg)
    log = open(os.path.join(out, "t", "drive.log")).read()
    print(log)
    assert len(launches) == 2, launches
    redo, rest = launches
    assert redo["steps"] == 1 and redo["resume"] and redo["tape"] == [None] * 3
    assert redo["tapes"] == [f"/c/rec-xs{{k}}-0-P{i}/step-0/tape_{i}.bin" for i in range(3)], redo["tapes"]
    assert redo["owner_msgs"] == [f"/c/rec-xs{{k}}-0-P{i}/step-0/owner-msg-P{i}.bin" for i in range(3)]
    assert polls["n"] >= 3, "the redo waited for its preprocessing"
    assert rest["steps"] == 1 and rest["resume"] and rest["tapes"] == [s["tapes"] for s in cfg["seats"]], rest
    assert serve[0] == {"exit": 0, "next_step": 3}
    assert "XT redo at step 1" in log and "XT redo of step 1 done; the steps after it resumed" in log and "run ended at step 3" in log
    st = json.load(open(os.path.join(out, "t", "xt_redo.json")))
    assert st == {"count": 1, "pending": None}, st
    # without xt_redo_tapes: refused by name, nothing launched
    cfg2, launches2, _, _, _ = scenario(with_redo_cfg=False)
    try:
        R.redo(cfg2, wait_s=0)
        raise AssertionError("redo without xt_redo_tapes must refuse")
    except SystemExit as e:
        assert "xt_redo_tapes" in str(e), e
    assert launches2 == []
    print("RUN.PY XT REDO: PASS")


if __name__ == "__main__":
    main()
