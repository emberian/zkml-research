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
| start | 2026-11-06 23:09Z | 59481839 | 50255943 B200 | 7.502 | accel-b200-mma-01 |  | cap $6.50, watchdog 50 min, image nvidia/cuda:12.9.1-devel-ubuntu24.04, credit before $27.70 |
| end | 2026-11-06 23:24Z | 59481839 | 50255943 B200 | 7.502 | accel-b200-mma-01 | $1.83 | est $1.91 over 15.3 min; destroyed+verified True; reason boot_timeout; credit after $25.87 |
| start | 2026-11-06 23:26Z | 59483602 | 50255943 B200 | 7.502 | accel-b200-mma-02 |  | cap $6.50, watchdog 50 min, image nvidia/cuda:12.9.1-devel-ubuntu24.04, credit before $25.79 |
| end | 2026-11-06 23:31Z | 59483602 | 50255943 B200 | 7.502 | accel-b200-mma-02 | $0.87 | est $0.72 over 5.7 min; destroyed+verified True; reason ssh_unreachable; credit after $24.92 |
| start | 2026-11-06 23:32Z | 59484211 | 56442968 H100 SXM | 2.278 | accel-h100-all-01 |  | cap $4.00, watchdog 95 min, image nvidia/cuda:12.9.1-devel-ubuntu24.04, credit before $24.92 |
| end | 2026-11-06 23:40Z | 59484211 | 56442968 H100 SXM | 2.278 | accel-h100-all-01 | $0.34 | est $0.30 over 7.8 min; destroyed+verified True; reason TimeoutExpired(['ssh', '-i', '/Users/ember/.ssh/id_ed25519', '-p', '29142', '-o', 'StrictHostKeyChecking=accept-new', '-o', 'UserKnownHostsFile=/Users/ember/.cache/accel-ready/vast_known_hosts.5948421; credit after $24.58 |
| start | 2026-11-06 23:41Z | 59485029 | 56442968 H100 SXM | 2.278 | accel-h100-all-02 |  | cap $4.00, watchdog 95 min, image nvidia/cuda:12.9.1-devel-ubuntu24.04, credit before $24.55 |
| end | 2026-11-06 23:56Z | 59485029 | 56442968 H100 SXM | 2.278 | accel-h100-all-02 | $0.75 | est $0.59 over 15.5 min; destroyed+verified True; reason ok; credit after $23.80 |
| start | 2026-11-07 00:19Z | 59488860 | 59433350 H100 SXM | 2.335 | accel-h100-mma-03 |  | cap $1.50, watchdog 39 min, image nvidia/cuda:12.9.1-devel-ubuntu24.04, credit before $23.67 |
| end | 2026-11-07 00:29Z | 59488860 | 59433350 H100 SXM | 2.335 | accel-h100-mma-03 | $0.38 | est $0.38 over 9.9 min; destroyed+verified True; reason ok; credit after $23.29 |
| start | 2026-11-07 00:31Z | 59490068 | 59157383 B200 | 12.510 | accel-b200-mma-03 |  | cap $7.00, watchdog 34 min, image nvidia/cuda:12.9.1-devel-ubuntu24.04, credit before $23.24 |
| end | 2026-11-07 00:38Z | 59490068 | 59157383 B200 | 12.510 | accel-b200-mma-03 | $1.25 | est $1.42 over 6.8 min; destroyed+verified True; reason ssh_unreachable; credit after $21.98 |
| start | 2026-11-07 17:33Z | 59603385 | 57922449 Tesla V100 | 0.267 | dl-gen6-cloud-seat-01 |  | cap $10.00, watchdog 1800 min, image nvidia/cuda:12.9.1-devel-ubuntu24.04, credit before $21.98 |
| start | 2026-11-07 17:34Z | 59603497 | 59433367 H100 SXM | 2.335 | accel-h100-tower-e2e-01 |  | cap $2.30, watchdog 57 min, image nvidia/cuda:12.9.1-devel-ubuntu24.04, credit before $21.98 |
