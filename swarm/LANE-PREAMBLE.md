# Common brief for zkml-research literature and pricing lanes

(Persistent copy, 2026-09-06. The scratchpad copy died with the 09-05 reboot.)

## Where you are
- Repo: /Users/ember/dev/zkml-research — RESEARCH NOTES ONLY. Companion implementation trees: /Users/ember/dev/minidregg (Lean, "Selvage"), /Users/ember/dev/breadstuffs (Rust). Do NOT modify either unless your brief says so. Do NOT git commit. Do NOT edit docs/VERDICTS.md (the coordinator folds).
- Read FIRST: SLVG_THOUGHT.md (shape), docs/VERDICTS.md §7 (open), notes/README.md (index). Then `grep -rli '<topic>' notes/ docs/ forcodex/` and READ the matching notes before claiming anything is new to us.

## House rules
- Every claim labeled: [READ] quoted at page/URL · [DERIVED] your arithmetic from named inputs · [INFERRED] your reconstruction · [OURS] proved/measured in our tree, cited by note. A number with no provenance does not go in.
- Absence claims name corpus AND instrument. Read the source, not a relay; a tweet is a tweet. Quote the pessimistic number.
- No "moat"/"scoop" vocabulary; other groups are collaborators.
- Write the note EARLY and update it incrementally; ≤ ~400 lines.

## Tools (absolute paths)
- Kagi: `python3 /Users/ember/dev/zkml-research/swarm/tools/kagi.py "<query>" [limit]` — metered; ≤ 25 queries per lane.
- Scry (public-internet-as-database, ClickHouse SQL): `SCRY_MAX_SECONDS=180 python3 /Users/ember/dev/zkml-research/swarm/tools/scry.py sql '<ONE SELECT ... LIMIT n>'`; `... call schema '{"relation":"openalex.works"}'` for a contract. Often congested: retry once, then move on. IACR eprint is NOT in scry.
- Local IACR eprint mirror: /Users/ember/dev/gh/forks/IACR-eprint-mirror/<year>/<id>.pdf (complete through 2026/1861 as of 09-05). NEVER download PDFs from eprint.iacr.org (the archive throttles); abstract pages at ≤ 1 request / 10 s and ≤ 40 per lane. `pdftotext` is installed; the Read tool reads PDFs with pages=.
- ~/paperbin/ holds previously collected PDFs. `gh api` is authenticated.

## Deliverable
One markdown file at the path your brief names, plus a ≤ 400-word report ending with: (1) verdict-changing findings, each pointing at the VERDICTS section it would change; (2) what you could NOT verify; (3) the corpus+instrument line for every absence claim.
