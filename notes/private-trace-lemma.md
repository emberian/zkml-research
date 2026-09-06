# private-trace-lemma — the multi-step, adaptive-policy lift of `post_public_agrees`

**Lane note, 2026-09-06.** Unit: `/Users/ember/dev/minidregg/Theory/PrivateTrace.lean` (new; the only
file touched). Sibling it extends: `/Users/ember/dev/minidregg/Kernel/PrivateTurn.lean` — cited by name
only; `Theory/` imports Mathlib alone (`scripts/check-import-boundary.sh` green).

## The statements (copied from the file)

Carrier — deterministic; randomized state needs a coupling version, NOT done:

```lean
structure Machine (S C O : Type*) where
  step : S → C → S
  out  : S → O
abbrev Policy (C O : Type*) := List O → C          -- adaptive: sees the outputs so far, oldest first
def trace (M : Machine S C O) (π : Policy C O) (s : S) (n : ℕ) : List O   -- the n observations;
  -- round k: observe `out` of the current state, append, step by π on the history so far.
  -- So observation 1 is `out s` itself.
theorem trace_length : (trace M π s n).length = n
```

The theorem:

```lean
theorem trace_eq_of_preserved (M : Machine S C O) (R : S → S → Prop)
    (hout  : ∀ s t, R s t → M.out s = M.out t)
    (hstep : ∀ s t c, R s t → R (M.step s c) (M.step t c)) :
    ∀ (π : Policy C O) (n : ℕ) (s t : S), R s t → trace M π s n = trace M π t n
```

`#print axioms`: **no axioms at all** (pure structural induction over rounds, generalising the
accumulated history).

The handoff's distinction, made the tree's: *certify the combined learn-and-infer interface, not the two
verbs independently* — `step` is "learn", `out` is "infer", and the invariant `R` must be simultaneously
blind to the query (`hout`) and stable under EVERY allowed update (`hstep`). `Kernel/PrivateTurn.lean`'s
`post_public_agrees` is the one-step hyperedge-shaped instance: its `hblind` is `hstep` for
`R := "equal public halves"`, its conclusion is `hout` after one step.

## The honest relation for the toy (byte machine, high-bit output)

`byteMachine off : Machine (Fin 256) C Bool`, `step s c = s + off c`, `out s = decide (128 ≤ s.val)`.
`flipMachine` = the single update `+128`.

The prompt's first guess `R s t := s % 128 = t % 128` (agree BELOW the high bit) is the wrong invariant:
`out` reads the high bit, so `hout` fails (`0` vs `128`) — and the file keeps it as the `hout`
falsifier (`lowR_flip_step` holds, `not_lowR_out`, `lowR_traces_differ`).

The honest relation is **equal high bit**: `highR s t := s.val / 128 = t.val / 128` — the states differ
only in their low seven bits. `highR_out` (the output is the high bit) and `highR_flip_step` (`+128`
flips both high bits together) — both `omega` over the byte bounds. Hence `flip_trace_eq_of_highR`: for
every policy and every length, `highR s t → trace = trace`. Distinct related states `0`, `5`
(`highR_zero_five`). The visible state DOES change: `flip_trace_alternates` — the trace from `s` is
`out s, ¬out s, out s, …` for all `n` (general induction, using `flip_out_step`); sample
`trace … 5 3 = [false, true, false]` decided. So "states differing only in lower bits remain
indistinguishable while the visible state changes" is a theorem, with the invariant named.

## The falsifier (handoff's) and the recovery result

**`hstep` is a constraint.** `twoMachine`: commands `flip (+128) | inc (+1)`. `highR` still satisfies
`hout` (`highR_two_out` — "equal answers to the next inference") but `inc` breaks preservation:
`not_highR_two_step` (`127 ↦ 128`, `0 ↦ 1`; both start with high bit 0). And the CONCLUSION fails:
`highR_two_traces_differ` — `highR 127 0` and, under "always `inc`", the two-observation traces
differ (`[false,true]` vs `[false,false]`). Equal next answers alone are insufficient.

**Recovery.** `offsetMachine`: commands `Fin 256` read as arbitrary offsets (contains `+1`, `+128`).
Binary-search policy `searchPolicy hist`: `k := hist.length`; if the last observed bit is `1`, offset
`256 − 2^(7−k)` (subtract), else `2^(7−k)` (add). Invariant: after the `k`-th command the state is
`(s mod 2^(8−k)) + 128 − 2^(7−k)`, whose high bit is bit `7−k` of `s`; so the eight observations are
`s`'s binary expansion, MSB first. Decoder `ofBits` (fold `2·acc + b`).

```lean
theorem search_recovers : ∀ s : Fin 256, ofBits (trace offsetMachine searchPolicy s 8) = s.val
theorem exists_policy_recovers :
    ∃ π : Policy (Fin 256) Bool, ∀ s t : Fin 256, trace offsetMachine π s 8 = trace offsetMachine π t 8 → s = t
```

Sharpness both ways: `search_seven_insufficient` (this policy: `0` and `1` agree on 7 observations) and
`no_policy_recovers_seven` — for EVERY policy, 7 boolean observations cannot separate 256 states
(pigeonhole through `List.Vector Bool 7`, `card_vector`/`Fintype.card_le_of_injective`). So 8 is the
exact number, not just this policy's number.

Scope caveat, stated: the recovery uses arbitrary offsets (the prompt's "or arbitrary offsets"). With the
alphabet `{+1, +128}` ALONE, 8 observations do not recover the byte (after k steps the reachable
states are `s + a + 128 b`, `a + b = k`, so only `s ≥ 128 − a` for `a ≤ 8` is ever tested); that
alphabet suffices for the `hstep` falsifier, which is what it is used for.

## Decided by kernel vs argued

- General arguments: `trace_eq_of_preserved`, `trace_length`, `flip_trace_alternates` (induction),
  `no_policy_recovers_seven` (pigeonhole), `exists_policy_recovers` (from `search_recovers`).
- `omega` over byte bounds: `highR_out`, `highR_flip_step`, `lowR_flip_step`, `flip_out_step`.
- `decide` (kernel, small): all concrete witnesses/falsifiers (`highR_zero_five`, `flip_trace_five`,
  `not_lowR_out`, `lowR_traces_differ`, `not_highR_two_step`, `highR_two_traces_differ`,
  `search_trace_178`, `search_seven_insufficient`, `searchPolicy_adaptive`).
- `decide +kernel` (256 bytes × 8 rounds): `search_recovers`. The 65,536-pair injectivity statement was
  NOT decided directly — it is derived from the 256-case decoder identity, which is stronger and cheaper.
- No `native_decide`, no `#guard`, no `sorry`/axiom. Twenty `#guard_msgs`-pinned `#print axioms`;
  the headline `trace_eq_of_preserved` and `eq_step` depend on no axioms; the rest on subsets of
  `[propext, Classical.choice, Quot.sound]`.

## Premise inhabitation

`machine_inhabited` (the byte machine); `eq_out`/`eq_step` (the identity relation satisfies both
premises for every machine — the uninteresting instance, relating no two distinct states, so its
conclusion is `trace s = trace s`; the content is in `highR`, which relates distinct states).

## Not done / possible follow-ups

- Coupling version for randomized state (named in the docstring as not done).
- "No NON-adaptive policy recovers in 8 observations" (8 fixed half-circle tests cut the byte circle
  into ≤ 16 arcs) — true, not formalised; only `searchPolicy_adaptive` records that the exhibited policy
  genuinely reads its history.
- Rooting in `Theory.lean` is the coordinator's (not touched here).

## Exact file list

- NEW: `/Users/ember/dev/minidregg/Theory/PrivateTrace.lean`
- NEW (this note): `/Users/ember/dev/zkml-research/notes/private-trace-lemma.md`
- Not touched: `Theory.lean`, `Kernel/PrivateTurn.lean`, everything else. Nothing committed.
