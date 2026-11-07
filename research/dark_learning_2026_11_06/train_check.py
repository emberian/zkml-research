"""Checks for the gen 6 step program (train lane).

    python3 -I train_check.py harness OLD_STEP_SPEC.py
        step_spec.step with the default program equals the step_spec at OLD_STEP_SPEC.py (e.g. `git show
        04d28e15:research/dark_learning_2026_11_06/step_spec.py`): outputs, traces and raised assertions, on random
        cases at d = 8 and 64 including out-of-bound ones; a control with another program differs.
"""
import hashlib
import importlib.util
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import step_spec as S


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def outcome(f, *a):
    try:
        return ("ok", f(*a))
    except AssertionError:
        return ("assert", None)


def harness(old_path):
    old = load(old_path, "step_spec_old")
    n = same = asserts = 0
    for d in (8, 64):
        r = random.Random(d)
        for case in range(40):
            wm = r.choice((1, 7, 7, 8))          # 8: out of the |W| <= 7 bound
            xm = r.choice((7, 7, 9))
            W1 = [[r.randint(-wm, wm) for _ in range(d)] for _ in range(d)]
            W2 = [[r.randint(-wm, wm) for _ in range(d)] for _ in range(d)]
            x = [r.randint(-xm, xm) for _ in range(d)]
            y = [r.randint(-7, 7) for _ in range(d)]
            a, b = outcome(old.step, W1, W2, x, y), outcome(S.step, W1, W2, x, y)
            n += 1
            same += a == b
            asserts += a[0] == "assert"
    ctl = S.Program(S2=3)
    r = random.Random(0)
    d = 64
    W1 = [[r.randint(-7, 7) for _ in range(d)] for _ in range(d)]
    W2 = [[r.randint(-7, 7) for _ in range(d)] for _ in range(d)]
    x = [r.randint(-7, 7) for _ in range(d)]
    y = [r.randint(-7, 7) for _ in range(d)]
    control_differs = S.step(W1, W2, x, y) != S.step(W1, W2, x, y, ctl)
    print(dict(cases=n, identical=same, of_which_asserted=asserts, control_differs=control_differs,
               old_sha256=hashlib.sha256(open(old_path, "rb").read()).hexdigest()))
    assert same == n and 0 < asserts < n and control_differs


if __name__ == "__main__":
    {"harness": harness}[sys.argv[1]](*sys.argv[2:])
