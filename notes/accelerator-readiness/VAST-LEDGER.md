# vast.ai rental ledger (initiative 17)

Rules (ember, 2026-11-06): $27 credit; stop at $25 total; one box at a time; spend cap and wall watchdog
per box; destroy at run end and verify absence via the API. Rows are written by `harness/vast_box.py`.
`cost` on an end row is the credit drop measured through the API (billing can lag a few minutes; the
rate x elapsed estimate is beside it).

| event | utc | instance | offer / type | $/h | label | cost | detail |
|---|---|---|---|---|---|---|---|
| start | 2026-11-06 22:46Z | 59479712 | 56928727 RTX 3060 Ti | 0.050 | accel-smoke-01 |  | cap $0.25, watchdog 15 min, image nvidia/cuda:12.4.1-base-ubuntu22.04, credit before $27.70 |
| end | 2026-11-06 22:56Z | 59479712 | 56928727 RTX 3060 Ti | 0.050 | accel-smoke-01 | $0.00 | est $0.01 over 10.4 min; destroyed+verified True; reason boot_timeout; credit after $27.70 |
| start | 2026-11-06 22:57Z | 59480687 | 55350610 RTX 3060 | 0.060 | accel-smoke-02 |  | cap $0.25, watchdog 15 min, image nvidia/cuda:12.9.1-devel-ubuntu24.04, credit before $27.70 |
| end | 2026-11-06 23:02Z | 59480687 | 55350610 RTX 3060 | 0.060 | accel-smoke-02 | $0.00 | est $0.01 over 5.2 min; destroyed+verified True; reason ok; credit after $27.70 |
