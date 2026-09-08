[EXECUTED] Commands were run from this package directory, using the existing local virtual environment. No package install, model download, fine-tuning or crypto rebuild occurred.

```sh
python3 -B get_data.py > data/selection.log
../../adaptation_utility/.venv/bin/python -B evaluate.py > evaluate.log 2> evaluate.stderr
../../adaptation_utility/.venv/bin/python -B encrypted_evaluate.py > encrypted_evaluate.log 2> encrypted_evaluate.stderr
../../adaptation_utility/.venv/bin/python -B full77.py > full77.log 2> full77.stderr
../../adaptation_utility/.venv/bin/python -B demo_cli.py plain > cli_demo_plain.log 2> cli_demo_plain.stderr
../../adaptation_utility/.venv/bin/python -B demo_cli.py bfv > cli_demo_bfv.log 2> cli_demo_bfv.stderr
../../adaptation_utility/.venv/bin/python -B encrypted_full77.py > full77/encrypted.log 2> full77/encrypted.stderr
```

[EXECUTED] The BFV `operations.jsonl` files record actual per-command arguments, returns and wall times. Benchmark private decode logs omit scalar stdout; aggregate comparisons and public-dataset predictions are separately saved. The eight-intent model's operations log subsequently grew with the separately recorded CLI interaction; its benchmark report retains the pre-interaction counts and costs.

[DERIVED] The one-shot batch scripts preserve prior outputs rather than silently overwriting their model directories. Continue using `learner.py` / `session.py` with the existing trained models, or initialize a new model directory.

[EXECUTED] The persistent-session demonstration ran `../../adaptation_utility/.venv/bin/python -B demo_session.py plain` and then `../../adaptation_utility/.venv/bin/python -B demo_session.py bfv`; exact stdin requests, argv, stdout, stderr and elapsed times are saved in session_plain.json/session_bfv.json. Their join is session_join_result.json.
