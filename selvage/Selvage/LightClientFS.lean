/-
# Selvage.LightClientFS — [LC-sound-fs]: the Fiat–Shamir-derived schedule inherits
# the light-client bound.

The LAST derandomization step. `Selvage/LightClientSound.lean` proved the one-shot
probabilistic light client over a UNIFORM i.i.d. challenge schedule
(`lightClientSound`, `n·(err⋆(δ) + 1/|F|)`; `lightClientSound_exact`, sharp
`1/|F|`). The deployed light client is NON-INTERACTIVE: it derives each link's
challenge by hashing the transcript prefix — Fiat–Shamir, σ-before-γ. This file
closes the transport: in the ROM (`Selvage/FiatShamir.lean`'s lazy-sampling
`Oracle` handler, REUSED not re-derived), the FS-derived schedule of a FIXED
chain is distributed EXACTLY as the uniform schedule, so both bounds transfer
VERBATIM to the non-interactive verifier.

The argument, in three proved steps:

* **Prefix distinctness (`linkPrefix_injective`) — the load-bearing fact.**
  Link `k`'s challenge is derived at the transcript prefix through link `k`
  (genesis + links `0..k`, roots and claims included — σ-before-γ: the link's
  commitment enters the hash before its challenge exists). Distinct links have
  prefixes of distinct LENGTHS, so the `n` derivation queries are pairwise
  distinct — the mirror of `SrOutput.query_injective` (Selvage/FiatShamir.lean),
  proved, not assumed. This is exactly what makes FS sound here: repeated or
  colliding queries would REPLAY logged coins and correlate the schedule.
* **Distinct fresh queries each draw their own coin
  (`Oracle.lookup_foldl_respond`).** The handler-fold law: folding `respond`
  over a duplicate-free list of pairwise-distinct queries, all fresh, logs
  every query with exactly its step's coin — lazy sampling answers each
  distinct fresh query with a FRESH uniform draw (`respond_fresh_*` iterated,
  with the frame law `lookup_respond_ne` insulating the earlier entries).
* **The transfer (`fsSchedule_fsDerive` → `fsSchedule_uniform`).** Therefore
  the FS-derived schedule, as the handler actually computes it
  (`fsSchedule (fsDerive A₀ ch c) A₀ ch d = c`), IS the fresh-coin tuple —
  whatever the lazy fallback `d`. The pushforward of the ROM's coin measure
  through the derivation is the uniform schedule measure ON THE NOSE, and
  `lightClientSound` / `lightClientSound_exact` fire unchanged:
  `lightClientFS_sound` (THE DEPLOYABLE NON-INTERACTIVE HEADLINE,
  `n·(err⋆(δ) + 1/|F|)`), `lightClientFS_exact` (sharp `1/|F|`),
  `lightClientFS_of_not_attests` (the `attests`-interface form).

**Keystones (F₅, computing, reusing `LCExample`/`LCSoundExample`):** the
phantom chain — the forger of the rigged schedule `(1,1)` — under the
FS-DERIVED schedule forges exactly when the ROM's coins land on the diagonal
(`phantom_fs_verifies_iff`): probability EXACTLY `1/5 = 1/|F₅|`
(`phantom_fs_forging_prob`, the exact bound ATTAINED), the general theorems
fire on it with every hypothesis discharged (`phantom_fs_caught_probably`,
`phantom_fs_delta_fired`), the true δ-event probability is computed
(`phantom_fs_delta_prob_eq` — union-bound slack visible), and both poles
compute: coins `(1,1)` forge, coins `(1,0)` catch — the verdict is the
ORACLE's doing. The honest chain verifies at probability 1
(`goodChain_fs_verifies_prob_one` — FS costs the honest prover nothing), and
its derived schedule is well-defined (= the coins) for every fallback.

**What this does NOT close (honest residuals, end of file):** the chain here
is FIXED before the oracle samples — the non-adaptive/honest-derivation form.
A `t`-query ROM adversary that GRINDS (chooses the chain after seeing oracle
answers) pays the `(t + n)` factor of WARP Thm B.4; that strengthening is
`[LC-fs-adaptive]`, riding `[ACC-sound-rbr]` + the landed `fsKeystone_proved`.
The hash-realizes-handler idealization stays `[FS-ROM]` (Selvage/FiatShamir.lean);
binding the prover's words to the fold stays `[ACC-extract]`.
-/
import Selvage.LightClientSound
import Selvage.FiatShamir

namespace Minidregg.Selvage

/-! ## The handler-fold laws: distinct fresh queries each draw their own coin

General `Oracle` vocabulary (Selvage/FiatShamir.lean's handler, its single-step
laws REUSED): what a fold of `respond` over pairwise-distinct fresh queries
logs. New vocabulary — no twin anywhere in the tree. -/

namespace Oracle

variable {Q C : Type}

/-- The fold-level frame law: folding `respond` over a query list never
disturbs a query outside it (`lookup_respond_ne` iterated). -/
theorem lookup_foldl_respond_ne {α : Type} (qs : α → Q) (cs : α → C) :
    ∀ (js : List α) (O : Oracle Q C) {q : Q}, (∀ j ∈ js, qs j ≠ q) →
      (js.foldl (fun O' j' => (O'.respond (qs j') (cs j')).2) O).lookup q
        = O.lookup q := by
  intro js
  induction js with
  | nil => intro O q _; rfl
  | cons a js ih =>
    intro O q hne
    rw [List.foldl_cons,
      ih _ (fun j hj => hne j (List.mem_cons_of_mem _ hj))]
    exact lookup_respond_ne O (Ne.symm (hne a (List.mem_cons_self ..))) _

/-- **Distinct fresh queries each get their own coin** — the lazy-sampling
uniformity at fold level: responding along a duplicate-free list of
pairwise-distinct queries, all fresh for the starting handler, logs every
query with EXACTLY its step's coin. Each distinct fresh query is answered by
a fresh uniform draw; nothing replays, nothing correlates. The engine of the
FS-schedule uniformity below. -/
theorem lookup_foldl_respond {α : Type} (qs : α → Q) (cs : α → C) :
    ∀ (js : List α) (O : Oracle Q C),
      (∀ j₁ ∈ js, ∀ j₂ ∈ js, qs j₁ = qs j₂ → j₁ = j₂) → js.Nodup →
      (∀ j ∈ js, O.lookup (qs j) = none) →
      ∀ j ∈ js,
        (js.foldl (fun O' j' => (O'.respond (qs j') (cs j')).2) O).lookup (qs j)
          = some (cs j) := by
  intro js
  induction js with
  | nil => intro O _ _ _ j hj; simp at hj
  | cons a js ih =>
    intro O hinj hnd hfresh j hj
    have hamem : a ∉ js := (List.nodup_cons.mp hnd).1
    have hne : ∀ j' ∈ js, qs j' ≠ qs a := fun j' hj' hq =>
      hamem (hinj j' (List.mem_cons_of_mem _ hj') a
        (List.mem_cons_self ..) hq ▸ hj')
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hj with rfl | hjmem
    · -- the head query: logged fresh with its coin, then framed off the tail
      rw [lookup_foldl_respond_ne qs cs js _ hne, lookup_respond_self,
        respond_fresh_fst (hfresh j (List.mem_cons_self ..)) _]
    · -- a tail query: still fresh after the head respond; recurse
      refine ih _ (fun j₁ h₁ j₂ h₂ =>
          hinj j₁ (List.mem_cons_of_mem _ h₁) j₂ (List.mem_cons_of_mem _ h₂))
        (List.nodup_cons.mp hnd).2 (fun j' hj' => ?_) j hjmem
      rw [lookup_respond_ne O (hne j' hj') _]
      exact hfresh j' (List.mem_cons_of_mem _ hj')

end Oracle

variable {Root ι : Type} {F : Type} [Field F] {r : ℕ}

/-! ## The light client's transcript prefixes -/

/-- The FS query type of the light client: the genesis statement together with
a chain prefix — what the non-interactive verifier hashes to derive one link's
challenge. Links carry their roots (the commitments) and claims, so the prefix
binds σ before γ; the WORDS behind the roots are bound by the commitment
layer (`[ACC-extract]` / `[FS-BCS]`), not hashed here. -/
abbrev LcQuery (Root F ι : Type) [Field F] (r : ℕ) : Type :=
  AccClaim Root F ι r × Chain Root F ι r

/-- **The round-`k` transcript prefix**: the genesis plus links `0..k` —
link `k`'s commitment and claim enter the hash BEFORE its challenge exists
(WARP's σ-before-γ sampling, rendered non-interactively). -/
def linkPrefix (A₀ : AccClaim Root F ι r) (ch : Chain Root F ι r) (k : ℕ) :
    LcQuery Root F ι r :=
  (A₀, ch.take (k + 1))

/-- The round-`k` prefix has length exactly `k + 1` — the mirror of
`SrOutput.query_pfx_length` (the growing transcript). -/
theorem linkPrefix_length (A₀ : AccClaim Root F ι r) (ch : Chain Root F ι r)
    {k : ℕ} (hk : k < ch.length) :
    (linkPrefix A₀ ch k).2.length = k + 1 := by
  simp only [linkPrefix, List.length_take]
  omega

/-- **Prefix distinctness — the load-bearing fact that makes FS sound here.**
Distinct links have distinct transcript prefixes (their lengths differ), so
the `n` derivation queries below are pairwise distinct and the lazy-sampling
handler answers each with a FRESH coin. A colliding prefix would REPLAY a
logged coin and correlate the schedule — exactly what this rules out. The
mirror of `SrOutput.query_injective` (Selvage/FiatShamir.lean). -/
theorem linkPrefix_injective (A₀ : AccClaim Root F ι r)
    (ch : Chain Root F ι r) {j k : Fin ch.length}
    (h : linkPrefix A₀ ch (j : ℕ) = linkPrefix A₀ ch (k : ℕ)) : j = k := by
  have hj := linkPrefix_length A₀ ch j.isLt
  rw [h, linkPrefix_length A₀ ch k.isLt] at hj
  exact Fin.ext (by omega)

/-! ## The FS-derived schedule -/

/-- **The FS-derived challenge schedule**: link `k`'s challenge is the oracle
at link `k`'s transcript prefix — `γ_k := O(A₀, links 0..k)` — read through
the handler's partial map with lazy fallback `d` (never consulted after an
actual derivation run: `fsSchedule_fsDerive`). The light-client instance of
`srFinalChal_eq_lookup`'s `lookup … |>.getD` shape. -/
noncomputable def fsSchedule (O : Oracle (LcQuery Root F ι r) F)
    (A₀ : AccClaim Root F ι r) (ch : Chain Root F ι r)
    (d : Fin ch.length → F) : Fin ch.length → F :=
  fun k => (O.lookup (linkPrefix A₀ ch (k : ℕ))).getD (d k)

/-- Non-degeneracy of the derivation: against the EMPTY handler the schedule
is all fallbacks — `fsSchedule` genuinely reads the oracle, so
`fsSchedule_fsDerive`'s "`= c` for every fallback" below is the RUN's doing
(every prefix logged), not a definitional accident. -/
@[simp] theorem fsSchedule_empty (A₀ : AccClaim Root F ι r)
    (ch : Chain Root F ι r) (d : Fin ch.length → F) :
    fsSchedule Oracle.empty A₀ ch d = d := by
  funext k
  show ((Oracle.empty).lookup (linkPrefix A₀ ch (k : ℕ))).getD (d k) = d k
  rw [Oracle.lookup_empty]
  rfl

/-- **The derivation run**: the non-interactive verifier's pass — starting
from the fresh handler, respond to each link's prefix in chain order, coin
`c k` at link `k`. This is the ROM actually SAMPLING the schedule (the
`srHandlerRun` discipline: coins come from the game's coin space, the handler
only records and replays). -/
noncomputable def fsDerive (A₀ : AccClaim Root F ι r) (ch : Chain Root F ι r)
    (c : Fin ch.length → F) : Oracle (LcQuery Root F ι r) F :=
  (List.finRange ch.length).foldl
    (fun O' (k : Fin ch.length) =>
      (O'.respond (linkPrefix A₀ ch (k : ℕ)) (c k)).2) Oracle.empty

/-- After the derivation run, every link's prefix is logged with exactly its
coin: the queries are pairwise distinct (`linkPrefix_injective`) and all fresh
for the empty handler, so `lookup_foldl_respond` applies. -/
theorem fsDerive_lookup (A₀ : AccClaim Root F ι r) (ch : Chain Root F ι r)
    (c : Fin ch.length → F) (k : Fin ch.length) :
    (fsDerive A₀ ch c).lookup (linkPrefix A₀ ch (k : ℕ)) = some (c k) := by
  unfold fsDerive
  exact Oracle.lookup_foldl_respond
    (fun j : Fin ch.length => linkPrefix A₀ ch (j : ℕ)) c
    (List.finRange ch.length) Oracle.empty
    (fun _ _ _ _ h => linkPrefix_injective A₀ ch h)
    (List.nodup_finRange _) (fun _ _ => Oracle.lookup_empty _)
    k (List.mem_finRange k)

/-- **The FS-derived schedule IS the fresh coins** — for EVERY lazy fallback
`d` (the fallback is never consulted: every prefix is logged). Distinctness
made the queries fresh; freshness made the responses the coins. This is the
whole transfer: the derivation is the identity map from ROM coins to
schedules. -/
theorem fsSchedule_fsDerive (A₀ : AccClaim Root F ι r)
    (ch : Chain Root F ι r) (c d : Fin ch.length → F) :
    fsSchedule (fsDerive A₀ ch c) A₀ ch d = c := by
  funext k
  show ((fsDerive A₀ ch c).lookup (linkPrefix A₀ ch (k : ℕ))).getD (d k) = c k
  rw [fsDerive_lookup]
  rfl

/-- **The FS schedule is uniform**: the pushforward of the ROM's coin measure
through the derivation run is the uniform schedule measure — every schedule
event has the SAME probability over FS-derived schedules as over uniformly
sampled ones. (`uniformProb_congr` along `fsSchedule_fsDerive`: the
pushforward realizer is the identity, so no mass moves at all.) -/
theorem fsSchedule_uniform [Fintype F] (A₀ : AccClaim Root F ι r)
    (ch : Chain Root F ι r) (d : Fin ch.length → F)
    (p : (Fin ch.length → F) → Prop) :
    uniformProb (Fin ch.length → F)
        (fun c => p (fsSchedule (fsDerive A₀ ch c) A₀ ch d))
      = uniformProb (Fin ch.length → F) p :=
  uniformProb_congr fun c => by rw [fsSchedule_fsDerive]

/-! ## The non-interactive light client: both bounds transfer verbatim -/

section Exact

variable (foldRoot : Root → F → Root → Root)

/-- **[LC-sound-fs], exact-word form**: a chain with ANY unsatisfiable link
survives the NON-INTERACTIVE verifier — challenges derived by the ROM at the
transcript prefixes — with probability at most `1/|F|` over the oracle's
coins. `lightClientSound_exact`'s sharp bound, inherited verbatim through
`fsSchedule_uniform`. -/
theorem lightClientFS_exact [Fintype F] {C : Submodule F (ι → F)}
    {A₀ : AccClaim Root F ι r} {ch : Chain Root F ι r}
    (halign : Aligned A₀ ch)
    (huns : ∃ l ∈ ch, ¬ ∃ f, AccClaim.Satisfies C l.claim f)
    (d : Fin ch.length → F) :
    uniformProb (Fin ch.length → F) (fun c =>
        Verifies C (aggregate foldRoot
          (padSched (fsSchedule (fsDerive A₀ ch c) A₀ ch d)) A₀ ch))
      ≤ 1 / (Fintype.card F : ℝ) := by
  refine le_of_eq_of_le (uniformProb_congr fun c => ?_)
    (lightClientSound_exact foldRoot halign huns)
  rw [fsSchedule_fsDerive]

/-- The `attests`-interface form: a seam-ok chain that does not attest
survives the non-interactive verifier with probability at most `1/|F|`. -/
theorem lightClientFS_of_not_attests [Fintype F] {C : Submodule F (ι → F)}
    {A₀ : AccClaim Root F ι r} {ch : Chain Root F ι r}
    (halign : Aligned A₀ ch) (hseam : SeamOk ch) (hnot : ¬ attests C ch)
    (d : Fin ch.length → F) :
    uniformProb (Fin ch.length → F) (fun c =>
        Verifies C (aggregate foldRoot
          (padSched (fsSchedule (fsDerive A₀ ch c) A₀ ch d)) A₀ ch))
      ≤ 1 / (Fintype.card F : ℝ) := by
  refine le_of_eq_of_le (uniformProb_congr fun c => ?_)
    (lightClientSound_of_not_attests foldRoot halign hseam hnot)
  rw [fsSchedule_fsDerive]

end Exact

section Proximity

variable [Fintype ι] [DecidableEq ι] [DecidableEq F]
variable (foldRoot : Root → F → Root → Root)

/-- **[LC-sound-fs], THE DEPLOYABLE NON-INTERACTIVE HEADLINE.** A history
chain carrying a δ-far-false link survives the non-interactive light client —
each link's challenge derived by the ROM at that link's transcript prefix,
σ-before-γ — with probability at most

  `ch.length · (err⋆(δ) + 1/|F|)`

over the oracle's coins: `lightClientSound`'s bound, UNCHANGED. The FS
derivation queries are distinct (`linkPrefix_injective`) and fresh, so the
derived schedule is distributed exactly uniformly (`fsSchedule_uniform`) and
the interactive bound transfers with no loss. Same anchoring as the uniform
form: the event sits at the honest fold of the committed words (`foldWords` —
binding the prover's recommitments to it is `[ACC-extract]`); the chain is
fixed before the coins sample (`[LC-fs-adaptive]` prices the grinding
adversary, end of file). -/
theorem lightClientFS_sound [Fintype F] [Nonempty ι] {C : Submodule F (ι → F)}
    {A₀ : AccClaim Root F ι r} {ch : Chain Root F ι r} {ws : List (ι → F)}
    {f₀ : ι → F} {δ dC Bstar : ℝ} {errstar : ℝ → ℝ}
    (halign : Aligned A₀ ch)
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hMCA : HasMutualCorrelatedAgreement (affineGenerator F) C Bstar errstar)
    (hδ0 : 0 < δ) (hδB : δ < 1 - Bstar) (hδC : δ < dC / 2)
    (herr0 : 0 ≤ errstar δ) (hlen : ws.length = ch.length)
    (hfalse : ∃ p ∈ ch.zip ws, ∀ v ∈ C, relDist p.2 v ≤ δ →
        ¬ AccClaim.Satisfies C p.1.claim v)
    (d : Fin ch.length → F) :
    uniformProb (Fin ch.length → F) (fun c =>
        ∃ w, relDist (foldWords
            (padSched (fsSchedule (fsDerive A₀ ch c) A₀ ch d)) f₀ ws) w ≤ δ ∧
          AccClaim.Satisfies C (aggregate foldRoot
            (padSched (fsSchedule (fsDerive A₀ ch c) A₀ ch d)) A₀ ch) w)
      ≤ (ch.length : ℝ) * (errstar δ + 1 / (Fintype.card F : ℝ)) := by
  refine le_of_eq_of_le (uniformProb_congr fun c => ?_)
    (lightClientSound foldRoot (f₀ := f₀)
      halign hdC hMCA hδ0 hδB hδC herr0 hlen hfalse)
  rw [fsSchedule_fsDerive]

end Proximity

/-! ## Keystones (ATLAS law 2: satisfiable + teeth + premise inhabitation)

All BUILT, computing where decidable, over `LCExample`/`LCSoundExample`'s
landed F₅ chains — REUSED, not rebuilt. The schedule is now the ORACLE's:
the phantom chain forges exactly when the ROM's coins land on the diagonal,
probability exactly `1/5 = 1/|F₅|` (bound attained); the honest chain
verifies at probability 1 whatever the oracle samples. -/

section KeystonePlumbing

/- Private mirror of Selvage/LightClientSound.lean's private keystone plumbing
(the module-private discipline: the aggregate build never sees two public
copies). -/
private theorem eq_of_relDist_le_of_lt_inv_card {ι : Type*} [Fintype ι]
    [Nonempty ι] {F : Type*} [DecidableEq F] {f u : ι → F} {δ : ℝ}
    (h : relDist f u ≤ δ) (hδ : δ < 1 / (Fintype.card ι : ℝ)) : f = u := by
  by_contra hne
  exact absurd (le_trans (one_div_card_le_relDist hne) h) (not_le.mpr hδ)

end KeystonePlumbing

namespace LCFSExample

open RSExample AccExample LCExample LCSoundExample

/-- Prefix distinctness COMPUTES on the keystone chain: the two links'
transcript prefixes differ (lengths 1 and 2) — the load-bearing distinctness,
witnessed concretely. -/
example : linkPrefix phantomGenesis phantomChain 0
    ≠ linkPrefix phantomGenesis phantomChain 1 := by
  intro h
  have hlen := congrArg
    (fun q : LcQuery (ZMod 5) (ZMod 5) (Fin 4) 1 => q.2.length) h
  exact absurd hlen (by decide)

/-- **Satisfiable side, schedule well-definedness**: the honest chain's
FS-derived schedule is exactly the ROM's coins, for every lazy fallback —
the derivation is total and deterministic given the oracle. -/
example (c d : Fin 2 → ZMod 5) :
    fsSchedule (fsDerive genesis goodChain c) genesis goodChain d = c :=
  fsSchedule_fsDerive genesis goodChain c d

/-- **Satisfiable side**: the honest keystone chain verifies under the
FS-derived schedule at probability 1 — non-interactivity costs the honest
prover nothing (completeness untouched by the oracle's sampling). -/
theorem goodChain_fs_verifies_prob_one (d : Fin 2 → ZMod 5) :
    uniformProb (Fin 2 → ZMod 5) (fun c =>
      Verifies (reedSolomonCode dom₅ 2)
        (aggregate linRoot
          (padSched (fsSchedule (fsDerive genesis goodChain c)
            genesis goodChain d))
          genesis goodChain)) = 1 := by
  refine Eq.trans (uniformProb_congr fun c => ?_) goodChain_verifies_prob_one
  rw [fsSchedule_fsDerive]
  exact Iff.rfl

/-- The phantom's forging set in COIN space, closed form: the FS-derived
aggregate verifies iff the ROM's two fresh coins are EQUAL — the diagonal
again, now as an event over the oracle's randomness. -/
theorem phantom_fs_verifies_iff (c d : Fin 2 → ZMod 5) :
    Verifies (reedSolomonCode dom₅ 2)
      (aggregate linRoot
        (padSched (fsSchedule (fsDerive phantomGenesis phantomChain c)
          phantomGenesis phantomChain d))
        phantomGenesis phantomChain)
    ↔ c 0 = c 1 := by
  rw [fsSchedule_fsDerive]
  exact phantom_verifies_iff c

/-- **Teeth — the forging probability under FS, EXACT**: the phantom chain
forges against the non-interactive verifier with probability exactly
`1/5 = 1/|F₅|` over the oracle's coins — `lightClientFS_exact`'s bound
ATTAINED. The chain that beat one rigged schedule loses to the ROM with
probability 4/5. -/
theorem phantom_fs_forging_prob (d : Fin 2 → ZMod 5) :
    uniformProb (Fin 2 → ZMod 5) (fun c =>
      Verifies (reedSolomonCode dom₅ 2)
        (aggregate linRoot
          (padSched (fsSchedule (fsDerive phantomGenesis phantomChain c)
            phantomGenesis phantomChain d))
          phantomGenesis phantomChain)) = 1 / 5 := by
  refine Eq.trans (uniformProb_congr fun c => ?_) phantom_forging_prob
  rw [fsSchedule_fsDerive]
  exact Iff.rfl

/-- **Premise inhabitation — the exact FS theorem FIRES on the phantom**:
`lightClientFS_exact` applied to the landed false chain, every hypothesis
discharged by landed witnesses, bound `1/5` — met with equality by
`phantom_fs_forging_prob`. -/
theorem phantom_fs_caught_probably (d : Fin 2 → ZMod 5) :
    uniformProb (Fin 2 → ZMod 5) (fun c =>
      Verifies (reedSolomonCode dom₅ 2)
        (aggregate linRoot
          (padSched (fsSchedule (fsDerive phantomGenesis phantomChain c)
            phantomGenesis phantomChain d))
          phantomGenesis phantomChain)) ≤ 1 / 5 := by
  have h := lightClientFS_exact linRoot phantomChain_aligned
    ⟨⟨0, 1, phantomClaim₀⟩, List.mem_cons_self ..,
      phantomClaim₀_unsatisfiable⟩ d
  simpa [ZMod.card] using h

/-- Coins `(1, 1)` — on the diagonal — FORGE: the oracle's answers rebuild the
rigged schedule of `LCExample.phantom_forged`. The verdict is the oracle's
doing, pole 1. -/
example : Verifies (reedSolomonCode dom₅ 2)
    (aggregate linRoot
      (padSched (fsSchedule (fsDerive phantomGenesis phantomChain ![1, 1])
        phantomGenesis phantomChain (fun _ => 0)))
      phantomGenesis phantomChain) :=
  (phantom_fs_verifies_iff ![1, 1] _).mpr (by decide)

/-- Coins `(1, 0)` — off the diagonal — CATCH the phantom: pole 2. -/
example : ¬ Verifies (reedSolomonCode dom₅ 2)
    (aggregate linRoot
      (padSched (fsSchedule (fsDerive phantomGenesis phantomChain ![1, 0])
        phantomGenesis phantomChain (fun _ => 0)))
      phantomGenesis phantomChain) :=
  fun h => absurd ((phantom_fs_verifies_iff ![1, 0] _).mp h) (by decide)

/-- **Premise inhabitation — the δ-headline FIRES non-interactively**: over
`C = ⊤` (mutual CA with `err⋆ = 0` from the landed
`hasMutualCorrelatedAgreement_top_affine`, `dC = 1/4` from
`minDistLB_inhabited`), the phantom prover's committed zero words carry a
δ-far-false link at `δ = 1/16`, and the FS-derived δ-proximity event is
bounded by `2·(err⋆ + 1/5) = 2/5` — every hypothesis of
`lightClientFS_sound` discharged by landed witnesses. -/
theorem phantom_fs_delta_fired (d : Fin 2 → ZMod 5) :
    uniformProb (Fin 2 → ZMod 5) (fun c =>
        ∃ w, relDist (foldWords
            (padSched (fsSchedule (fsDerive phantomGenesis phantomChain c)
              phantomGenesis phantomChain d)) 0 [0, 0]) w ≤ 1 / 16 ∧
          AccClaim.Satisfies (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
            (aggregate linRoot
              (padSched (fsSchedule (fsDerive phantomGenesis phantomChain c)
                phantomGenesis phantomChain d))
              phantomGenesis phantomChain) w)
      ≤ 2 / 5 := by
  have hmax : max (1 - 1 / (Fintype.card (Fin 4) : ℝ) / 2) 0 = 7 / 8 := by
    rw [Fintype.card_fin, max_eq_left (by norm_num)]
    norm_num
  have h := lightClientFS_sound linRoot (f₀ := (0 : Fin 4 → ZMod 5))
    (ws := [0, 0]) (δ := 1 / 16) phantomChain_aligned
    (minDistLB_inhabited _) hasMutualCorrelatedAgreement_top_affine
    (by norm_num) (by rw [hmax]; norm_num) (by norm_num [Fintype.card_fin])
    (le_refl 0) rfl
    ⟨(⟨0, 1, phantomClaim₀⟩, 0), List.mem_cons_self ..,
      fun v _ hclose => ?_⟩ d
  · have h' : (2 : ℝ) * (0 + 1 / 5) = 2 / 5 := by norm_num
    rw [← h']
    simpa [ZMod.card] using h
  · rintro ⟨-, hc⟩
    have h0v : (0 : Fin 4 → ZMod 5) = v :=
      eq_of_relDist_le_of_lt_inv_card hclose (by norm_num [Fintype.card_fin])
    have h1 := hc 0
    rw [← h0v] at h1
    exact absurd h1 (by decide)

/-- The FS δ-event's TRUE probability: exactly `1/5` — the union bound's
factor-of-`n` slack stays visible in the non-interactive form (`2/5` claimed,
`1/5` true), exactly as in the uniform form. The transfer moved no mass. -/
theorem phantom_fs_delta_prob_eq (d : Fin 2 → ZMod 5) :
    uniformProb (Fin 2 → ZMod 5) (fun c =>
        ∃ w, relDist (foldWords
            (padSched (fsSchedule (fsDerive phantomGenesis phantomChain c)
              phantomGenesis phantomChain d)) 0 [0, 0]) w ≤ 1 / 16 ∧
          AccClaim.Satisfies (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
            (aggregate linRoot
              (padSched (fsSchedule (fsDerive phantomGenesis phantomChain c)
                phantomGenesis phantomChain d))
              phantomGenesis phantomChain) w)
      = 1 / 5 := by
  refine Eq.trans (uniformProb_congr fun c => ?_) phantom_delta_prob_eq
  rw [fsSchedule_fsDerive]
  exact Iff.rfl

end LCFSExample

/-! ## Ledger, and what remains of [LC-sound-fs] (honest residuals, prose)

**Closed here** (no sorry, no new axioms):

* `linkPrefix_injective` — the prefix DISTINCTNESS, a real proof (prefix
  lengths grow), not an assumption: the fact that makes FS sound at all.
* `Oracle.lookup_foldl_respond` (+ the fold frame law) — distinct fresh
  queries each draw their own coin: the lazy-sampling handler's fold-level
  uniformity, built on FiatShamir's single-step laws.
* `fsSchedule_fsDerive` / `fsSchedule_uniform` — THE TRANSFER: the FS-derived
  schedule of a fixed chain IS the fresh-coin tuple (every fallback), so its
  distribution is uniform on the nose and every schedule event keeps its
  probability. The pushforward realizer is the identity — no measure
  machinery needed, which is exactly what distinctness+freshness buy.
* `lightClientFS_sound` / `lightClientFS_exact` /
  `lightClientFS_of_not_attests` — both light-client bounds, inherited
  VERBATIM by the non-interactive verifier: `n·(err⋆(δ) + 1/|F|)` and the
  sharp `1/|F|`. `[LC-sound-fs]` is closed at this (fixed-chain) level: the
  deployable non-interactive form carries the proved numbers.

**Remaining, named, with realizers:**

* **[LC-fs-adaptive]** — the chain here is FIXED before the ROM samples: the
  derivation's `n` queries are the oracle's ONLY queries, and the adversary
  does not see coins before committing the chain. A grinding adversary — `t`
  oracle queries, chain chosen afterwards — re-derives schedules until one
  forges, paying the union bound over its queries: WARP Thm B.4's
  `(t + k)·ε_rbr` shape, PROVED in general as `FsOfRbrSound`/
  `fsKeystone_proved` (Selvage/FiatShamir.lean, unconditional). Consuming it
  here needs the light-client per-fold bounds packaged as an RBR round
  function — `[ACC-sound-rbr]` (named in Selvage/AccSound.lean), the same
  packaging `[ACC-extract]` rides. Nothing about the BOUND SHAPE changes;
  the price becomes `(t + n)·(err⋆ + 1/|F|)` for a `t`-query adversary.
* **[FS-ROM]** (inherited, Selvage/FiatShamir.lean) — the deployed hash
  realizing the lazy-sampling handler is the one named idealization; domain
  separation of `LcQuery` from the stack's other oracle uses is priced there.
* **[ACC-extract]** (unchanged, Selvage/Accumulator.lean) — events here anchor
  at the honest fold of committed words; binding a forging prover's
  recommitments to that fold is the erasure-extraction obligation.

**Audit notes (does the FS schedule GENUINELY inherit the bound?).** The
inheritance rests on exactly two facts, both proved: (1) the derivation
queries are pairwise DISTINCT — `linkPrefix_injective`, by the growing prefix
length, mirroring `SrOutput.query_injective`; a collision would replay a coin
and the diagonal event below would inflate; (2) distinct fresh queries draw
independent fresh coins — `Oracle.lookup_foldl_respond`, from the landed
handler laws. Non-vacuity is computed: the transfer is exercised end-to-end
on the phantom chain, whose FS forging event is EXACTLY the coin diagonal
(`phantom_fs_verifies_iff`) at probability exactly the sharp bound
(`phantom_fs_forging_prob` = `1/5`), with both poles decided (coins `(1,1)`
forge, `(1,0)` catch). The general theorems fire with all hypotheses
discharged (`phantom_fs_caught_probably`, `phantom_fs_delta_fired`), the true
δ-probability is computed (`phantom_fs_delta_prob_eq` — slack visible), and
the honest chain pays nothing (`goodChain_fs_verifies_prob_one` = 1). The
fallback argument `d` of `fsSchedule` is universally quantified everywhere —
the theorems hold for EVERY fallback because the derivation logs every
prefix, so no conclusion smuggles strength through the default. -/

end Minidregg.Selvage

