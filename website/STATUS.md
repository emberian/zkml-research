# Research website — published

[EXECUTED, 2026-09-08] The site is live at
https://emberian.github.io/zkml-research/. Root enabled GitHub Actions Pages,
pushed the reviewed site at88e4b780 and verified successful workflow34186886811.
The six served HTML/assets/manifests match the local build byte for byte;
deployment metadata `.nojekyll` returned404 and is recorded separately.
Root checked the live desktop page and expanded source links through native
Chrome/CUA. `deployment.json` retains the HTTP, hash and workflow evidence.

[EXECUTED interface] It has ten evidence cards, three reading paths, search, topic/type
filters, URL-restored filters, no-results/reset behavior, deep links and native
expandable evidence. All result summaries retain explicit limitations.

[EXECUTED construction-lane ownership] The construction lane changed only `website/` and the new
`.github/workflows/pages.yml`. It did not edit shared research ledgers, root
README, VERDICTS or companion trees, commit, push, change repository settings,
publish, or run research experiments. The source facts are the earlier completed
evidence, not the ongoing third-run results.

## Reproduced checks

[EXECUTED command]

```sh
python3 website/build.py
python3 website/build.py --check
python3 -m py_compile website/build.py website/serve.py website/check_remote.py
actionlint .github/workflows/pages.yml
python3 website/check_remote.py
```

[EXECUTED output] Build and check both pass: ten cards, 18 locked excerpts,
56 HTML link/asset references and seven generated public files. The artifact
is approximately 59 KB, including its JSON manifests. Python syntax and
`actionlint` both exit zero. The remote checker fetched 14 distinct immutable
GitHub evidence blobs; all returned 200 and all complete SHA-256 values matched.
Its local detailed output is in ignored `qa/remote-links.json`.

[EXECUTED browser] Playwright Chromium reviewed the desktop at 1440×1050 and
mobile at 390×844. Both have no horizontal overflow. Screenshots were visually
inspected at `qa/desktop.png`, `qa/mobile.png`, `qa/mobile-evidence.png`,
`qa/desktop-evidence.png` and `qa/reading-paths.png` (ignored). The initial
missing-favicon 404 was fixed with the local typographic icon. A fresh navigation
then reported zero console errors and loaded only the page, stylesheet, script
and favicon from the local preview origin.

[EXECUTED browser controls] The interaction run returned:

```json
{"proofCount":3,"openProofCount":1,"openProofId":"pq-composition","emptyVisible":true,"resetCount":10,"searchCount":1,"restoredQuery":"BFV","restoredCount":1,"evidenceExpanded":true}
```

[EXECUTED progressive enhancement] A new browser context with JavaScript
disabled returned `noJsCards=10`, `noJsFiltersHidden=true` and
`noJsEvidenceWorks=true`. Opening an incompatible filtered URL with
`#semantic-bfv` reveals that card and resets the filter. Keyboard Tab first
reaches “Skip to content”; Enter focuses `main` after the focus-target repair.

[EXECUTED preview boundary] HTTP checks returned 200 for the project root and
script. `/README.md`, `/zkml-research/../README.md`, encoded-parent traversal
and an asset-directory listing all returned 404. The server reads only the
generated directory. The live local preview is
`http://127.0.0.1:4173/zkml-research/`; root may stop it after review.

[DERIVED limits of these checks] This is browser inspection and meaningful
build/interaction validation, not a formal accessibility certification. Source
hashes establish which evidence was read; they do not prove the research claims.
The allowlisted static artifact excludes raw source notes, runtime data and
private profile material. The public blob check confirms linked evidence was
already available at the recorded commits when checked.

[EXECUTED publication scope] Publication is complete. Subsequent result-card
changes require reading the completed evidence and refreshing the reviewed
source locks; ongoing experiments are not imported automatically.
