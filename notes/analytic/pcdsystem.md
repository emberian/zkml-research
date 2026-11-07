# pcdsystem lane (2026-11-07)

Branch `lane/pcdsystem` on minidregg, worktree `/Users/ember/dev/minidregg-lanes/pcdsystem`.
Sub-lanes: `lane/pcdsystem-u8` (item 2, composed proof system at U8) and `lane/pcdsystem-darkimp`
(item 3, single-provider impossibility), each with its own notes file beside this one.

## Ground truth used (real signatures, read before building)
- `Selvage/Rbr.lean`: `Reduction` (:144; one `W`, one `PMsg`, one finite `Chal`, `k` rounds, `R`/`R'` over an
  implicit word `Fin n → A`, δ-relaxed by `RelaxedMem`), `KStateFn` (:235; `empty_iff`, `prover_monotone`,
  `full_iff`), `RbrKnowledgeSoundness` (:281; backward `extract`, `err i st δ`, `extract_sound`),
  `StraightlineSrKnowledgeSoundness r Z εsr` (:415).
- `Selvage/Depth.lean`: `OB2_depth_composition_nonneg_proved : OB2_depth_composition_nonneg`
  (RBR ⇒ straightline SR knowledge, error `(t + k)·εrbr`, the game-slot method).
- `Selvage/FiatShamir.lean`: `FsOfRbrSound`, `fsOfRbrSound_iff_depth`.
- `Selvage/AccRbrInstance.lean`: the accumulator CHAIN as a `Reduction`, one round per link (the object
  generalized here). `Selvage/ConstrainedCode.lean`: `card_batch_satisfying_le` (reused for the node bound).
- `Selvage/HeteroComposition.lean`: `(t+k)·ε` composes rounds of ONE reduction, not proof-system layers.
  This is why the DAG is built as one reduction.
- breadstuffs `Dregg2/Circuit/RecursiveAggregation.lean` is a named-hypothesis attestation result
  (`EngineSound`), not a probabilistic knowledge statement; not built on.
- Cost model: `Assurance/CostModel.lean` (costmodel lane, `b01fbec35`), merged into this branch.

## Item 1: DAG PCD (landed, `Selvage/DagPcd.lean`, `Assurance/DagPcdPrice.lean`)
- `dagReduction S G`: one round per node in topological order; source relation = every local claim
  witnessed; target = every sink accumulator witnessed; verifier recomputes accumulators (`accAt`).
- Knowledge state over the LIVE frontier (processed nodes that are sinks or still feed an unprocessed node).
  Shared nodes stay owed until their last consumer; the full transcript owes exactly the sinks.
- `dagRbr`: Def 4.2 with round error `S.err (fan-in)`. `dag_round_bad_sub` reduces the round-bad event to
  the node's bad event.
- `dag_pcd_knowledge_sound`, `dag_pcd_fs_knowledge_sound`: `(t + N)·ε`, ε ≥ every node error.
  Per node, depth-free, shared nodes paid once.
- `linScheme`: shared-functional γ-fold, oracle words in the statement, error `a/|F|`. Diamond over ZMod 7:
  the honest statement is accepted at all 2401 challenge vectors; a false one at exactly 343 (ρ₁ = 0), which
  attains 1/7. `diamond_bad_statement_false`: the bad statement has no witness at all.
- Shapes: `chainDag`, `treeDag` (queue-merge), `scanDag T B` (Mina: per-block trees plus a ledger chain).
  With 1024 leaves: edges 1023 / 2046 / 2047, depth 1024 / 11 / 38. Fold term at ud100: 145 / 144 / 144 bits,
  so the decider's 100 bits bind. At BabyBear⁴ (ir2): 83 / 82, so 100-bit aggregation needs the degree-6
  challenge field.

## Codex review (gpt-6-astra, once) and what changed
- Found: the first `linScheme` was vacuous. Every target had a witness when φ ≠ 0, and extractors are
  unbounded, so knowledge was free. Fixed: oracle words in the statement, false statements exist.
- Found: the claim "extraction time Σ etᵢ" was unsupported (`extractTime` is bookkeeping; `accAt` is not
  memoized). Withdrawn.
- Confirmed: the live frontier is correct; `node_sound` is the right (demanding) premise; the bound is per
  node and depth-free; the cap is min(1, (t+N)ε).
- Scope recorded in the header: an IOR-resolution verifier (it sees all messages); compliance is per node
  (predecessor consistency is the application's to encode); the one-oracle flattening of in-circuit hashing
  is named, not proved; committed WARP/WHIR needs relaxed relations and oracle-reading extractors before it
  instantiates `AccScheme`.
- Next (Codex's sharpening): `t·ε_max + Σᵢ εᵢ`, i.e. `(t·a_max + |E|)/|F|` for linScheme. This needs a
  heterogeneous-error variant of OB-2′.

## Calculus lane alignment
Sent: my rule prices per node under one oracle (RBR premises); their `recurse` is the per-edge rule for
independently compiled arguments. On a DAG with sharing the two differ exactly on shared nodes.
Suggested a second rule, `recurse_rom`, whose conclusion is `(t + #rounds)·max ε`.
