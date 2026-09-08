# Continuing support-ticket learner

Teach labels from examples, then classify new text. The encoder stays fixed; each label learns a 576-dimensional prototype from its eight most recent examples. New labels become available immediately. Model directories persist across commands.

Run with the existing local environment from this directory:

```sh
PY=../../adaptation_utility/.venv/bin/python
$PY learner.py init models/my_tickets
$PY learner.py teach models/my_tickets --label card_arrival --text 'My new card has still not arrived.'
$PY learner.py teach models/my_tickets --label lost_card --text 'I lost my debit card yesterday.'
$PY learner.py query models/my_tickets --text 'When will the card I ordered be delivered?'
$PY learner.py status models/my_tickets
```

Use `init models/my_encrypted_tickets --backend bfv` for encrypted prototype state and encrypted dot products. Text encoding runs locally in plaintext. The CLI recipient holds the full decryption key; class names/counts and query features are public. This research tool does not provide restricted release or a private encoder.

[EXECUTED] The eight-intent benchmark reached 269/320 final correct; all 6,400 encrypted integer scores matched the plaintext computation. The unchanged full 77-intent learner reached 2,253/3,080 (73.1494%) with 1,232 continuing teaches. See REPORT.md for the complete progression, regressions and encrypted scope. The trained plaintext model is models/full77; models/bfv is the eight-intent BFV model plus the demonstrated ninth account_access class. The complete BFV model at models/full77_bfv now contains all 77 benchmark classes plus the live-taught loan_application class (78 total); all 5,929 benchmark integration scores and 155 live-session scores matched.

For continuing interaction without reloading the encoder for every command, run `$PY session.py models/my_tickets` and send one JSON object per line:

```json
{"op":"teach","label":"account_access","text":"I forgot my app password and cannot log in."}
{"op":"query","text":"How do I reset the code I use to sign in?"}
{"op":"status"}
```

The same session interface accepts an encrypted model directory. Use one writer per model directory.

Accuracy numbers refer to the benchmark checkpoints before the subsequent live class additions. Encrypted models retain operation traces on disk; the eight-example limit bounds active class memory, not the archived trace.
