# Research website — published; evidence update prepared

[EXECUTED root publication preparation, 2026-09-08T05:30:48.965405+00:00] Research checkpoint cf0f91f is public. Strict production build and reproducibility check pass:11 cards,25 excerpts,64 references,7 files,68,680bytes. All 19 distinct immutable GitHub source blobs return200 and match complete hashes. Root inspected the new desktop evidence and mobile PQ screenshots. Preview draft markers are absent from the production manifest. The eight reviewed website changes are ready for deployment; the earlier draft-only paragraph below is historical.

[EXECUTED update preparation, 2026-09-08] A new local preview contains eleven
cards and 25 reviewed source excerpts. The public-coin card now reports the
completed 40 Learn / four Infer / eight expiry journal and 44 independent
replays. The emitted nonlinear sample and older fourteenth-Learn replay failure
have separate cards; the latter includes the five separately completed fixed-FFT
controls without attributing the old cause or claiming plaintext correctness.
The PQ card reports conditional packed sizing examples and no certified bits.
The underway successor contributes no result to this page. VERDICTS and the
checked-but-unlanded formal proposal retain their existing scope.

[EXECUTED update checks] `python3 website/build.py --preview --refresh-sources`
and `python3 website/build.py --preview --check` pass: eleven cards, 25 excerpts,
64 HTML link/asset references, seven output files and 67,676 public bytes.
Python syntax checks pass. The first preview command rejected an endpoint one
line beyond the PQ report; the range was corrected to complete paragraphs before
locking. The selected source documents are linked, never copied into the site.

[EXECUTED update browser] Playwright Chromium inspected 1440×1050 desktop and
390×844 mobile. Screenshots `qa/update-desktop.png`,
`qa/update-desktop-evidence.png`, `qa/update-mobile.png`,
`qa/update-mobile-failure.png` and `qa/update-mobile-pq.png` are ignored local
review artifacts. No horizontal overflow, console error or remote page resource
was observed. The interaction check waits for the existing 120 ms search debounce;
an initial immediate count attempted before that debounce was corrected in the
check, with no application change needed.

```json
{"all":11,"proof":3,"openProof":"pq-composition","fftSearch":"nonlinear-replay-boundary","restoredSearch":"FFT","restoredCount":1,"empty":true,"reset":11,"keyboardEvidence":true,"sourceLinks":3,"deepLinkReveals":true,"deepLinkResets":"all","firstFocus":"Skip to content","skipTarget":"main","noJsCards":11,"noJsFiltersHidden":true,"noJsEvidence":true,"noJsOverflow":false}
```

[EXECUTED publication boundary] Ten excerpt references currently use the explicit
draft mode because their evidence is not committed. Strict build refuses the
untracked source; the remote checker refuses a draft manifest before network
access. Both leave the preview intact. Preview mode still rejects parent
traversal, hidden repository metadata, runtime, archive and stopped-task paths.
`qa/update-build-boundaries.json` retains these results. Source commits and the
subsequent immutable remote-blob check belong to root's publication sequence.
This preparation changes only `website/`; it does not commit, push or deploy.

[EXECUTED historical evidence] `deployment.json` is unchanged at SHA-256
`71f366c0998fa09babab97bd6e4bc78f3a0691644efe1e9ec0a3d57d4bc384ee`.
The record below describes the earlier ten-card publication, not this draft.

## Initial publication

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
