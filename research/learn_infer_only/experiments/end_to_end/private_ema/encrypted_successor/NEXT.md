# Resume/check the one scheduled run

[EXECUTED stopped] The first execution stopped at a real byte mismatch on
event `h0-e0014`, not a session-lifetime interruption. Read `REPORT.md` and
`reports/run001/public_failure_audit.json`. All processes have exited. Do not
resume, retry, relaunch or run the private drain on this frozen workload.

[EXECUTED] Launcher PID 38570 began 04:12:26 UTC; root tool session was 66721.
Actual public process is PID 38579. Check `reports/run001/progress.json`,
`run.stdout`, `run.stderr` and any `reports/run001/failure.json` before acting.
Do not restart a partial crypto workload or edit the frozen programs.

[OPEN] Root owns a separate public-log/source audit of the byte-determinism
failure. It may inspect only public ciphertext/metadata and pinned sources;
the failed outputs remain unopened. Preserve the first failure and its partial
runtime. Semantic correctness remains unassessed for this run.

[OPEN] If a frozen checker has a metadata bug, preserve its failure and fix
only a separate successor checker against the same bytes. Never rerun a
successful crypto workload merely to repair report packaging.
