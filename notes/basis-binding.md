# Ordered-basis binding for the additive-FRI transcript

Lane: LEAN + TRANSCRIPT, 2026-08-16. Closing `keystone_basis_ambiguity`.

⚠ **The brief's file path was wrong, and this is the first finding.** The brief located
the controller at `~/dev/breadstuffs/metatheory/Dregg2/Circuit/Emit/…
Compiler/Tower256AdditiveFriController.lean`. There is **no** `Tower256*` or
`*FriController*` file anywhere under `breadstuffs/metatheory`. The real cone is
**`~/dev/minidregg/Compiler/`**:

| object | file |
|---|---|
| the controller | `/Users/ember/dev/minidregg/Compiler/Tower256AdditiveFriController.lean` (428 lines) |
| the Raw sibling controller | `/Users/ember/dev/minidregg/Compiler/Tower256AdditiveFriRawController.lean` |
| the Raw deployment (the only inhabitant) | `/Users/ember/dev/minidregg/Compiler/Tower256AdditiveFriRawDeployment.lean` (289 lines) |
| the clause the controller verifies | `/Users/ember/dev/minidregg/Compiler/AdditiveFriReceiptClause.lean` |
| the counterexample | `/Users/ember/dev/minidregg/Selvage/AdditiveBaseFold.lean:786` |
| the downstream obligation | `/Users/ember/dev/minidregg/Selvage/RingSwitching.lean:505` |

---

## 1. What the transcript binds today — READ, not inherited

### 1a. The Fiat–Shamir input, exactly

`Tower256AdditiveFriController.challengeInput` (line 207) is

```
envelope pins.statementBytes ++
  flatten [ envelope (encodeLength n) ++ envelope (digestCodec.encode root_n) | n ≤ j ]
```

and `queryPrefix` (line 224) is the same with all `m+1` roots plus
`flatMap (envelope ∘ valueCodec.encode) challenges`. The Raw sibling
(`Tower256AdditiveFriRawController.lean:184,200`) is byte-for-byte the same shape.

So the complete sponge input is: **`statementBytes` · roots · challenges.** That is all.

### 1b. `clause.tower.beta` exists and enters nothing

`AdditiveFriTower` (`Selvage/AdditiveFriQuery.lean:74`) carries
`beta : ℕ → F`, `offset : F`, `independent`, `rounds_le`. The clause re-exposes it
first-order: `AdditiveFriReceiptClause.Clause` has

```
basis      : Nat → F
basisExact : basis = tower.beta
offset     : F
offsetExact: offset = tower.offset
basisOrder : BasisOrder
basisOrderExact : basisOrder = .reversedHighCoordinateFirst
```

— so the statement **has** the ordered basis. `grep beta Compiler/Tower256AdditiveFri*.lean`
returns **nothing**: no transcript function reads it.

### 1c. The "`domainId`" the brief named is two different things, and neither is the basis

- `LevelSpec.domainId : Digest` (controller line 55) is an opaque per-level metadata
  label handed to `backend.towerPort` / `additiveMerkleScheme`. In the only
  inhabitant it is `levelId 2 level = ⟨970000 + 4*level + 2⟩`
  (`Tower256AdditiveFriRawDeployment.lean:59,68`) — **a function of the level index
  alone.** It does not mention `beta`, `offset`, or even `ell`.
- `TranscriptPins.challengeDomainId` / `queryDomainId` (controller line 197–199) are
  **cSHAKE namespace separators**, not the evaluation domain at all. Their only
  obligation is `domainIdsDistinct`.

So the brief's summary ("binds a sponge `domainId`, not a basis") is right in
substance but the object is weaker than it sounds: the deployed `domainId` does not
even bind the *domain*.

### 1d. ⚑ The docstring that carries the whole obligation, and its only inhabitant refutes it

`TranscriptPins.statementBytes : List UInt8` has the docstring

> "The statement bytes **must** include the complete manifest/clause statement
> encoding selected by the artifact."

That is a **comment**. There is no field, no hypothesis, and no theorem anywhere
relating `statementBytes` to `clause.basis`, `clause.tower.beta`, or the clause at
all. And the repository's only inhabitant sets

```
bootstrapPins.statementBytes := [0x6d,0x69,0x6e,0x69,0x64,0x72,0x65,0x67,0x67]   -- "minidregg"
```

— nine constant ASCII bytes encoding no statement whatsoever. So the obligation is
not merely undischarged in general; the one witness on disk **violates it**.

**Measured verdict: the additive-FRI transcript binds the ordered basis nowhere,
and the seam where it was supposed to happen is a free `List UInt8` guarded by prose.**

---

## 2. The binding, and the canonical encoding — named, because the encoding IS the binding

`Compiler/Tower256AdditiveFriController.lean`, new:

```lean
abbrev transcriptValueCodec : LawfulCodec Tower256 := BinaryTower256Profile.profile.valueCodec

def basisFrame (index : Nat) (value : Tower256) : List UInt8 :=
  envelope (encodeLength index) ++ envelope (transcriptValueCodec.encode value)

def basisPrefix (ell m : Nat) (basis : Nat → Tower256) (offset : Tower256) : List UInt8 :=
  envelope (encodeLength ell) ++ envelope (encodeLength m) ++
    envelope (transcriptValueCodec.encode offset) ++
      (List.ofFn fun index : Fin ell => envelope (basisFrame index (basis index))).flatten
```

**Five decisions, each of which is the binding:**

1. **Positional, with the index INSIDE the frame.** Each element is
   `envelope (encodeLength index) ++ envelope (encode value)`, wrapped in its own
   envelope, laid down in index order. Anything set-shaped — a sorted list, an XOR
   fold, a multiset of hashes — would agree on the span and differ on the order,
   which is the hole one level down that the brief warned about.
2. **`offset` is bound too.** The domain is affine (`AdditiveFriTower.offset`);
   binding only `beta` would leave the domain itself unpinned.
3. **`ell` and `m` are bound**, so the frame count is not inferable-and-therefore-
   forgeable.
4. **One codec, named once.** `transcriptValueCodec` is the same Fan–Paar codec
   `queryPrefix` already used for challenges. Two canonical encodings of one object
   is how the hole comes back.
5. **The whole prefix is spliced inside ONE envelope** (`basisBinding`), so the
   sponge input peels cleanly and the binding is structural — there is no
   caller-side obligation to forget, unlike `statementBytes`.

Spliced into **both** sponge inputs of **both** controllers:

| function | before | after |
|---|---|---|
| `Tower256AdditiveFriController.challengeInput` | `envelope stmt ++ roots` | `envelope stmt ++ basisBinding ++ roots` |
| `Tower256AdditiveFriController.queryPrefix` | `envelope stmt ++ roots ++ challenges` | `envelope stmt ++ basisBinding ++ roots ++ challenges` |
| `Tower256AdditiveFriRawController.challengeInput` | same shape | same splice |
| `Tower256AdditiveFriRawController.queryPrefix` | same shape | same splice |

The Raw sibling matters most: it is the **only inhabited** deployment path
(`Tower256AdditiveFriRawDeployment`). It imports `basisPrefix` rather than
re-deriving it.

Injectivity, proved from the tree's existing envelope machinery
(`parseEnvelope_envelope_append`, `envelope_injective`, `lawfulCodec_encode_injective`):

```
envelope_append_inj · encodeLength_injective · basisFrame_inj
flattenFrames_append_inj   -- a run of enveloped frames is recovered FRAME BY FRAME, IN ORDER
basisPrefix_inj            -- ell, m, offset, and basis index for every index < ell
```

## 3. The closure — theorems, in both directions

### Selvage: `Selvage/AdditiveBasisBinding.lean` (new, 483 lines)

| name | says |
|---|---|
| `table_unique_of_novelPack_eq` | ⭐ at a FIXED ordered basis, the codeword determines the Boolean table |
| `novelPack_congr` | the packing reads `β` only on `[0, l)`, so a FINITE ordered tuple suffices |
| `table_unique_of_basis_agree` | ⭐ two bases agreeing on the live range ⇒ one table — the form a transcript can discharge |
| `no_span_indexed_decoder` | ⚑ **no** `decode : Submodule → codeword → table` is correct on honest commitments |
| `lchBasisBoundPcs` / `_complete` / `_extractable` | ⭐ the repaired handle carries the ORDERED basis, and is Complete + Extractable |
| `lchRingSwitchTarget` | ⭐ a `RingSwitchTarget` from the actual LCH packing |
| `spanBoundPcs` / `_complete` | the unrepaired handle (domain + codeword), still complete |
| `spanBoundPcs_not_extractable` | ⚑ **`Extractable` is FALSE** for it, at GF(16) |

`keystone_basis_ambiguity` is the **specification**: every negative above is proved
by feeding it exactly that counterexample (`preA`/`preB`, `keystoneBeta`/
`keystoneBetaSwap`, `sharedWord = X² + X`), and every positive is the statement the
counterexample refutes with the basis unbound.

⚑ **The floor is satisfiable AND refutable.** `lchBasisBoundPcs_extractable` and
`spanBoundPcs_not_extractable` are the two halves. An `Extractable` that could not
be refuted would be a tautology; the pair is what makes it a check.

### Compiler: the weld

```lean
theorem challengeInput_determines_basis :
  challengeInput … clause … = challengeInput … other … →
    clause.tower.offset = other.tower.offset ∧
      ∀ index, index < ell → clause.tower.beta index = other.tower.beta index

theorem transcript_determines_table :
  (same challenge input) → novelPack clause.tower.beta arity (mobius table) = word →
    novelPack other.tower.beta arity (mobius otherTable) = word → table = otherTable
```

Both exist in **both** controllers. `transcript_determines_table` is the brief's
requested form: *two commitments accepted under the same transcript determine the
same table.* Before the splice it was FALSE by `keystone_basis_ambiguity`; the
sponge input mentioned `basis` nowhere, so the two orderings shared a transcript.

## 4. `Extractable` discharged and WIRED

`RingSwitching.lean` §7 item 4:

> "Ring-switching's `Extractable` is FALSE for a scheme with that ambiguity —
> extraction is not unique — so this is a blocking prerequisite, not a hygiene note."

Discharged by `lchRingSwitchTarget`, and wired to the deployed object rather than
left as a lemma:

```lean
noncomputable def clauseRingSwitchTarget (clause : FriClause pcs m manifest) :
    RingSwitchTarget Tower256 := lchRingSwitchTarget clause.tower.beta

theorem clauseRingSwitchTarget_extractable : (clauseRingSwitchTarget pcs clause).pcs.Extractable
theorem clauseRingSwitchTarget_commit : … .commit table = ⟨arity, clause.tower.beta, novelPack …⟩ := rfl
```

So a clause on the deployed path *names* an extractable Π′, and by
`challengeInput_determines_basis` two clauses sharing a transcript name Π′s that
agree at every live index.

⚠ **Not an identity carrier.** The prior inhabitant, `RingSwitching.trivialTarget`,
has `Root = Σ l, table` — its handle IS the witness, so `extractable` is
`fun rt => ⟨rt.2, …⟩`, content-free. Here the handle is the packed codeword and
extraction runs through `novelPack_injective_of_natDegree_lt`;
`spanBoundPcs_not_extractable` shows the proof genuinely uses the `basis` field.

## 5. Teeth

| tooth | where | asserts |
|---|---|---|
| mutation is real | `keystone_reordering_is_a_real_mutation` | `keystoneBeta ≠ keystoneBetaSwap` **and** their `additiveDomain`s are EQUAL — i.e. the change is real *and* the old binding is provably blind to it |
| mutation is real (byte layer) | `tooth_reordering_is_a_real_mutation` | the two Tower256 orderings differ at index 0 and are a permutation of one another |
| honest ACCEPTED | `tooth_honest_accepted` | the repaired scheme accepts the true evaluation of the true table at every point — not a blanket refusal |
| reordered REFUSED | `tooth_reordered_refused_at_corner` | at the corner where the tables disagree, the honest handle rejects `preB`'s value outright |
| handles differ | `tooth_handles_differ` + `tooth_words_agree` | the two handles differ, and their committed CODEWORDS are literally equal — so it is the binding doing the work, not the data |
| transcript differs | `tooth_reordered_transcript_differs` | `basisPrefix 2 m toothBasis 0 ≠ basisPrefix 2 m toothBasisSwap 0` |

The mutation-is-real assertions come **before** the verdicts, per the
falsifier-that-stopped-falsifying discipline: if `keystoneBetaSwap` ever stopped
being a genuine reordering, or its domain stopped matching, the teeth would be
measuring nothing and would say so.

Accept-side regression: `Tower256AdditiveFriRawDeployment.bootstrapReceipt_accepts`
and `honest_run_succeeds` still build against the spliced definitions — a splice
that refused honest work would take them red. ⚠ **Honest caveat**: the bootstrap is
`m = 0`, `queryCount = 0`, so its `Accepts` proof is quantified over `Fin 0` and the
accept-tooth from that object is **vacuous**. The non-vacuous accept-tooth is
`tooth_honest_accepted` in Selvage, plus `challengeInput_eq_of_samePrefix` — the
roots-before-challenges schedule property, which is the thing a prefix splice could
actually have broken, and which still holds.

## 6. Flag day — measured, and it is empty

A transcript change alters the Fiat–Shamir input, so every additive-FRI challenge
and query seed changes. What re-emits:

- **No Rust consumer.** `grep -rn "challengeInput|queryPrefix|AdditiveFri" prover/src
  native` → **zero hits**. `prover/tests/additive_fri_reference.rs` no longer exists
  (only stale `prover/target` fingerprints mention it).
- **No `@[export]`** on any declaration in either controller → nothing crosses the
  FFI boundary.
- **No golden transcript bytes** anywhere in the tree.
- **`transcriptControllerDigest` does not re-derive**: its values are hand-assigned
  registry naturals (`⟨0⟩`, `⟨713⟩`, `⟨93014⟩`), with no computed relation to the
  controller's bytes. *(That is itself a finding: a "controller digest" that pins
  nothing about the controller.)*
- **The only Lean inhabitant** is the zero-round bootstrap, which still builds.

**Verdict: nothing deployed uses the additive path, so the flag day is a rebuild
and nothing re-emits.** Full `lake build` at HEAD (`37c6b33`) + this patch: **8946 jobs, green.**

## 7. Residuals, stated rather than absorbed

1. ⚑ **The `statementBytes` class is closed only for the basis.** The docstring
   obligation ("must include the complete manifest/clause statement encoding") is
   still prose for everything else — manifest/declaration identity, the degree and
   rate schedules. `Accepts` checks those against the clause, so the residual is a
   *statement-identity* binding, not a second basis hole. Same fix shape:
   structural splice, not a comment.
2. **`Extractable` remains the zero-error idealization** `RingSwitching.lean`
   already labels as undone work; `lchBasisBoundPcs`'s handle is the codeword
   polynomial, not a Merkle root, and `accepts` is the ideal "some table packs to
   this word". What is proved is that the **decode map is well defined** — which is
   exactly the layer item 4 blocks at — **not** that FRI proximity or Merkle binding
   realize it. Succinctness, position binding and proximity are untouched.
3. ⚠ **`Selvage/RingSwitching.lean` §7 item 4 still reads as an open blocker.** It
   needs a one-line update pointing at `lchRingSwitchTarget`. **Deliberately not
   edited**: a concurrent lane holds ~215 uncommitted lines in that file, and
   `git commit --only` is path-granular, so touching it would sweep their work into
   this commit. Left for whoever lands that lane.

## 8. Verification method

Built in a **detached worktree at HEAD (`37c6b33`)** (`git worktree add --detach`, `.lake`
cloned COW), not the shared working tree — which at the time carried a concurrent
lane's **red** `Selvage/RingSwitching.lean` (763 lines vs 568 at HEAD;
`Unknown identifier div_add_div_same` at line 534). That lane's diff does not touch
`LargeFieldMlePcs`, `Extractable`, `RingSwitchTarget` or `trivialTarget`, so this
work is compatible with both versions — but the green here is HEAD's green, not the
working tree's.

Every new theorem carries a `#print axioms` pin: `[propext, Classical.choice,
Quot.sound]`, no `sorry`, no `native_decide`, no new axioms.

