# Independent review of the private EMA dynamics extension

[DERIVED review decision] **Accepted for the stated finite-history, per-bin
integer-dynamics claims; no blocking issue found.** The proof reuses the frozen
word operation and does not replace it with an independently defined learner.
The six-update count, consistency premise, initial invariant, signed-floor
rounding and bounded fixed-point claim are all present in the actual theorem
statements. No semantic-encoder utility or cryptographic conclusion follows.

[DERIVED reviewer scope] This reviewer authored the imported
`PrivateAddressEma` word module in an earlier assignment, but did not author
`PrivateEmaDynamics`. This is an independent audit of the new dynamics proof
and its dependency identity, not a second independent semantic review of the
base word module or of the emitted-schedule successor. Neither author package
nor the companion tree was modified.

[EXECUTED exact targets] Source
`formal/private_ema_dynamics/Theory/PrivateEmaDynamics.lean` has SHA256
`4cfad9f0326ba5ff7a13e871a6d56a82816d0746592248aa84cda40fcae56bfb`;
its patch has SHA256
`da4e1d75e0e7ff2843a598c008ba4126fcc3885ffa2529adb099eaf807ab8e1b`.
The imported source is exactly
`0b148bff8a53447bc9f30950948771a4b0f53edeb1110cc78f44e85a960d562d`,
and its prerequisite patch is exactly
`9fabd5d64ab3280dde1bbb1affab9ced9d5835f248f984dd4bb9d0488622ebae`.
All 23 author-manifest entries were rehashed and their lengths checked.

[EXECUTED independent validation] The command
`python3 research/learn_infer_only/experiments/adversarial_review/private_ema_dynamics/audit.py`
produced [`run_001/report.json`](run_001/report.json), all passed. In a new
temporary source copy it applied the prerequisite patch and then the dynamics
patch, compared both applied modules byte-for-byte with the frozen sources,
and passed the companion's import-boundary script. It freshly compiled both
proposed modules with Lean 4.30.0, including the dynamics module's **28 exact
axiom guards**, with empty stdout and stderr. Only cached external dependency
oleans were reused; this was not a clean dependency build or umbrella build.
The explicit qualified-name census also reports 28 declarations and 28 pins,
no forbidden constructs, and only the standard `propext`, `Classical.choice`
and `Quot.sound` axiom subsets. Input hashes and companion HEAD/status remain
unchanged. Individual commands and outputs are retained beside the report.

[SOURCE inspected proof] All locations in this paragraph refer to the frozen
`Theory/PrivateEmaDynamics.lean`. `SixConsistentSign` at line 32 states the
claim before its proof. `candidate_monotone` at line 57 uses signed `toInt`
order and the inherited exact floor equation, so there is no accidental
unsigned ordering or omitted wrap premise. `advance_monotone` at line 62
lifts this to every natural iteration count. The kernel-checked opposite
endpoints at lines 84 and 87 become +11 and -14 after six updates; lines 90
through 120 compare every permitted initial selected byte to those endpoints
and preserve the correct sign for every larger consistent count.

[SOURCE inspected quantifiers] `history_target_subsequence` at line 122 is
an induction over arbitrary finite event lists. An event at the queried bin
contributes exactly one existing `candidate` update; an off-bin event vanishes
from that bin through `learn_untouched`. Consequently `six_consistent_sign`
at line 160 counts **at least six updates to this selected bin**, all with the
same actual ±120 byte. It does not count elapsed time or all route events,
and it does not assume a majority vote. Off-bin labels in this segment may be
arbitrary signed bytes: no `AllowedHistory` premise is imposed on them. This
freedom is a property of the selected-bin result; it does not promise a global
`Within120` invariant for every other bin after unrestricted labels.

[SOURCE inspected suffix and retention] `consistent_suffix_sign` at line 177
allows every earlier finite history whose labels satisfy `AllowedHistory`,
starting from `Within120`. It obtains the new initial invariant from the
already proved `history_invariant`, then applies the per-bin theorem to the
later consistent segment. `untargeted_retention` at line 144 is stronger in
a different direction: a never-targeted cell retains its exact original byte
through every finite history, without any label restriction or range premise.

[SOURCE inspected teeth and inhabitation] Lines 216–222 exhibit failures after
five consistent updates in both directions, including actual `infer` outputs.
These establish that five cannot replace six uniformly on `Within120`; they
do not say that every initial state needs six. `six_step_premises_inhabited`
at line 234 supplies all keystone premises together. The changed-state and
interleaved subjects at lines 248 and 254 are nonempty and retain another cell.
Neither the positive theorem nor its displayed witnesses rely on an empty
accepted set or an impossible range assumption.

[SOURCE inspected quantization] `floor_residual` at line 210 proves the scaled
one-step residual lies in [-7,0] for every pair of signed bytes. `fixed_points`
at line 185 restricts its input to [-120,120]: under that restriction the +120
fixed points are 113 through 120 and the -120 fixed point is only -120.
The bounded qualification matters: over the full signed-byte domain, the
negative-label fixed points also include -127 through -121. The 25-step
zero-state calculation at line 227 is a concrete pair of settled trajectories,
not a theorem that every initial state reaches those particular endpoints
in 25 steps, nor a claim that 25 is minimal.

[EXECUTED independent integer controls] The separate
[`integer_controls.py`](integer_controls.py) uses Python integers and `// 8`,
with no BitVec, gate, Rust, TFHE, model or private-data calls. The retained
[`run_001/integer_controls.json`](run_001/integer_controls.json) checks all
65,536 signed-byte input pairs for the one-step residual and byte range,
65,280 adjacent-state comparisons for monotonicity, and all 241 invariant
initial values in both label directions for the six/five-step boundary and
fixed-point sets. It reproduces the endpoint trajectories
`-120,-90,-64,-41,-21,-4,11` and `120,90,63,40,20,2,-14`.
Local frame controls are finite checks only; arbitrary interleavings are
established by the inspected induction, not by enumerating those checks.

[REFUTED: two tempting weakened statements] The integer controls also record
two distinct quantifier counterexamples. From selected value -120, one +120
update at the target followed by five updates elsewhere leaves the target
at -90: six total events are insufficient. Five +120 target updates followed
by a -120 target update leave it at -19: six target events without the
consistency premise are insufficient. These are controls on interpretations
of the theorem, not attacks on the implementation or a field-wide verdict.

[OPEN boundaries and next action] The result is about an ideal finite sequence
of the existing typed word operations and its declared sign output. It does
not prove that semantic labels are correct, that input issuance is authorized,
that an encrypted workload has utility, that TFHE gates decrypt correctly,
that ciphertext bytes replay deterministically, or that reader credentials
are restricted. It says nothing about an infinite run or a subsequently
inconsistent targeted segment. Root can fold this scoped acceptance into the
shared ledgers and run combined-umbrella integration; no author repair or
cryptographic rerun is required by this review.

[EXECUTED search accounting] Web, Scry, Kagi, PDF, model and cryptographic
calls: zero.
