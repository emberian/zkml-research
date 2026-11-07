# native/: the dark-learning MPC fork as a native system

Rust port of `research/dark_learning_2026_11_06/` (the Python harness stays the bit-exact reference: every native
output equals the harness output for the same seed). Decision doc: `docs/DARK-LEARNING-SCHEME-DECISION.md` §§13-23.

| crate | what |
|---|---|
| `pycompat` | CPython `random.Random` (MT19937, int/str seeding, getrandbits, randrange, randint, choice) and `repr()` streamed into SHA-256, bit-exact (`tests/vs_python.rs` runs python3) |
| `darkstep` | SPDZ online phase, ideal dealer tapes, BFV (RNS/NTT) and the HE matvec/outer helpers, the step program, three custodian processes over sockets |
| `dzkpopk` | the batched Ligero ZKPoPK and the key ceremony |
| `darkproof` | the collaborative ZK proof (cozk, spine, middle) and the untrusted-input verifier/ledger |
| `darkprep` | real preprocessing (replacing the ideal dealer) |

Build with your own target dir when lanes run in parallel: `CARGO_TARGET_DIR=target-<lane> cargo build --release -p <crate>`.
Never run an unfiltered `cargo test`; filter with a test name or `-p <crate> --test <name>`.
