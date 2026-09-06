# Combined proposed Lean integration

[EXECUTED] Run the finished-proposal integration with:

```sh
python3 research/learn_infer_only/experiments/integration/check_all_formal.py --checks
```

The command's actual results are in `results/latest.json`, which points to a
numbered run's `report.json`. Each subprocess has a separate JSON log containing
the exact command, working directory, exit code, stdout/stderr, elapsed time, and
the Lean search path when applicable. Failed runs are retained.

[EXECUTED] The preserved baseline is `results/run_001/report.json`: twelve modules,
217 pins, four umbrellas, and both integer executable checks passed. The combined
baseline patch is also retained as
`../../formal/integration/minidregg-combined-resident-217.patch`. The separate
`modules_with_ema.json` adds the stable four-module, 48-pin EMA tranche. Run it with:

```sh
python3 research/learn_infer_only/experiments/integration/check_all_formal.py \
  --manifest research/learn_infer_only/experiments/integration/modules_with_ema.json
```

This second pass rebuilds the selected proof modules together in a fresh overlay;
the unchanged integer executable checks retain their first-pass evidence.

[DERIVED: tooling scope] `modules.json` is the explicit inclusion boundary. Its
nine finished lane patches identify twelve proposed modules with 217 expected
theorem pins. The tool discovers each new source destination from the selected
patch, checks it against the current proposed source byte for byte, and sorts the
modules and four umbrella modules by imports. Extend the manifest with another
finished patch and its expected pin count; no scanner silently promotes in-flight
files. EMA, the new Garner-certificate work, optimizer work, and separate review
witnesses are excluded from the initial manifest. The finished large-integer QR
module is included.

[DERIVED: isolation] Every run copies all current tracked and nonignored untracked
Lean sources from `/Users/ember/dev/minidregg`, plus its import-boundary script,
into an owned scratch tree. It preserves the companion's current dirty umbrella
bytes, initializes a separate Git repository there, generates one combined patch,
executes both `git apply --check` and `git apply`, and compares every patched file
to the intended contents. Independent lane patches are never rewritten. The
boundary script runs over that complete applied source copy and over the original
companion, read-only.

[DERIVED: build scope] All twelve proposed modules and the Theory, Compiler,
Selvage, and Assurance umbrellas elaborate sequentially into one fresh overlay.
Existing dependency artifacts are linked read-only. Namespace directories are
fully populated because Lean does not fall back per module from a partial first
search-path namespace. Every newly compiled output is a local regular file, never
a companion symlink. This checks integration against the existing dependency
oleans; it is **not a clean build of the companion or its dependencies**. It also
does not establish runtime refinement, cryptographic assumptions, or the truth of
uncompiled source changes behind a cached dependency.

[DERIVED: census scope] `axiom_census.json` records each theorem, its source line,
the exact expected axiom message, and the guarded name. The lexical scan masks
comments and strings, matches every theorem/lemma to one axiom pin, and rejects
unguarded prints, custom axiom sets, and the listed forbidden constructs. Lean
then elaborates each actual source with its `#guard_msgs` checks. The accepted
axiom vocabulary is `propext`, `Classical.choice`, and `Quot.sound`, with an empty
list retained where proved. This is a census of the selected modules, not the
entire dependency closure.

[DERIVED: executable checks] `--checks` additionally compiles the two integer
`Checks` modules in a separate scratch hierarchy. Their `#eval` output paths stay
inside this lane's scratch tree. Generated JSON is copied to the numbered result
directory and hashed. These executable harness modules are not imported by the
four umbrellas and are not part of the proposed combined patch.

[EXECUTED: provenance instrument] Each report records before/after hashes of the
selected sources, lane patches, manifest, checker, environment record, and all
copied companion Lean sources. Companion HEAD and `git status --short` are recorded
before and after. Cached dependency artifact paths, sizes, and mtimes are recorded
separately; dependency oleans are reused, not rebuilt. No Scry/Kagi queries are
needed for this local integration check.
