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

(sections 2–6 appended as the work lands)
