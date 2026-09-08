# Public research index

[DERIVED design] A small, static guide to existing evidence. This directory is
presentation code and curated navigation, not another research-truth ledger.
`docs/VERDICTS.md` remains authoritative. Newer resident experiments are labeled
as scoped results; the site does not promote them into whole-system guarantees.

[EXECUTED implementation] Python standard library and Git build the site.
The browser receives HTML, CSS, a small script, a typographic icon, and two JSON
manifests. It requires no package installation, external fonts, analytics,
API, account, or server-side application. JavaScript adds search and two filters;
the full evidence and native expandable source links work without it.

## Build and preview

```sh
python3 website/build.py
python3 website/build.py --check
python3 website/serve.py --port 4173
```

[EXECUTED interface] Open `http://127.0.0.1:4173/zkml-research/`. The preview
server exposes only `website/dist/`, under the project base path; it does not
serve the repository. Python 3.10 or newer is sufficient for the used standard
library APIs; the Pages workflow selects Python 3.12. `dist/`, local screenshots
and browser QA artifacts are ignored.

## Evidence changes

[DERIVED maintenance rule] `catalog.json` holds short presentation summaries,
reading paths and an explicit list of public source excerpts. Every card has an
evidence category and a visible limitation. The selected excerpt's SHA-256 is
locked in `source-lock.json`. When a selected excerpt changes, the ordinary
build stops; it never updates the lock automatically.

1. Read the changed evidence and the current verdicts. Reconcile the card's
   wording, scope, denominators and evidence category.
2. Update the selected line range and review date in `catalog.json` as needed.
   Preserve complete paragraphs and the limiting assumptions.
3. After that review, run `python3 website/build.py --refresh-sources` and inspect
   the named lock changes. Commit new source evidence before production build.
4. Run `python3 website/build.py --check` and review the affected card in a browser.

[EXECUTED build behavior] Source files must already be Git-tracked, not ignored,
not symlinks, and within the explicitly permitted public evidence roots. The
builder refuses runtime/archive/stopped-task paths. It never copies source
documents or experiment directories into the public artifact. Source links
resolve to the last commit for that path only after its selected excerpt is
compared with those committed bytes. The manifest records the linked complete
blob hash, excerpt hash, revision, path and line range. `--preview` permits a
reviewed, uncommitted excerpt locally using a branch link; the workflow never
uses that flag.

[EXECUTED validation] The build verifies local assets, fragments, unique IDs,
curated external URL membership, source locks and basic private/local-data
markers in the generated files. `--check` regenerates in memory and rejects any
missing, additional or differing output file. The output allowlist is the
primary publication boundary; a marker scan is supplementary, not a secret
detector for arbitrary research trees.

[EXECUTED optional network check] To fetch each distinct, immutable public
evidence blob and compare its full SHA-256 with the manifest:

```sh
python3 website/check_remote.py
```

[DERIVED scope] This performs read-only requests to GitHub's raw content host.
It is intentionally separate from the offline build and ordinary CI. New
evidence commits must be pushed before their remote links can pass.

## GitHub Pages publication

[SOURCE: official documentation read, 2026-09-08] The prepared workflow follows
[GitHub's custom Pages workflow](https://docs.github.com/en/pages/getting-started-with-github-pages/using-custom-workflows-with-github-pages):
build, upload the static artifact, then deploy through a job depending on the
successful build. The deployment uses the `github-pages` environment, `pages:
write` and `id-token: write`. The Pages documentation currently illustrates
`configure-pages@v5`, `upload-pages-artifact@v4` and `deploy-pages@v4`.

[SOURCE: official documentation read] Repository Pages must use **GitHub
Actions** as its publishing source. See
[Configuring a publishing source](https://docs.github.com/en/pages/getting-started-with-github-pages/configuring-a-publishing-source-for-your-github-pages-site).
The workflow publishes only on `dev` pushes or a manual dispatch from `dev`;
pull requests build/check without deployment. It uploads **only** `website/dist`.

[DERIVED publication handoff] The root agent owns the final review, named-file
commit, push, Pages setting and deployment verification. This lane has prepared
the workflow but has not changed GitHub settings, pushed, or deployed. The
intended URL is `https://emberian.github.io/zkml-research/`; its availability must
be established by the actual deployment, not this note.

[DERIVED optional root README insertion, after publication]

```markdown
- [Research website](https://emberian.github.io/zkml-research/) — a guided index
  of result cards, evidence and limitations, with three reading paths.
```

[EXECUTED source access accounting] Site construction used one primary web
search and four direct official documentation/repository opens. The separate
public evidence check fetched 14 distinct immutable repository blobs. No Scry,
Kagi, eprint PDF, or literature search was used for this presentation task.
