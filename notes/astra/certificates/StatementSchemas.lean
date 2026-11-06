import Lean

/-!
Typed statement targets for the certificate audit, not claims of completed
cryptographic proofs. Defining a Prop below does NOT prove it. Every context is
explicit; probabilistic laws use a single supplied experiment. A production
instance must implement the experiment and justify its resource admissibility.
-/
namespace Astra.CertificateStatements

universe u

structure ContentScheme (Sym Digest Op LenOp : Type) where
  commit : List Sym → Digest
  openAt : List Sym → Nat → Op
  openLen : List Sym → LenOp
  verifyOpen : Digest → Nat → Sym → Op → Bool
  verifyLen : Digest → Nat → LenOp → Bool
  complete : ∀ w i (h : i < w.length),
    verifyOpen (commit w) i w[i] (openAt w i) = true
  lengthComplete : ∀ w, verifyLen (commit w) w.length (openLen w) = true

variable {Sym Digest Op LenOp : Type}
variable (S : ContentScheme Sym Digest Op LenOp)

inductive BindingWitness where
  | word (u v : List Sym)
  | position (c : Digest) (i : Nat) (v v' : Sym) (o o' : Op)
  | length (c : Digest) (n m : Nat) (o o' : LenOp)

def BindingWin : BindingWitness (Sym := Sym) (Digest := Digest)
    (Op := Op) (LenOp := LenOp) → Prop
  | .word u v => S.commit u = S.commit v ∧ u ≠ v
  | .position c i v v' o o' =>
      S.verifyOpen c i v o = true ∧ S.verifyOpen c i v' o' = true ∧ v ≠ v'
  | .length c n m o o' =>
      S.verifyLen c n o = true ∧ S.verifyLen c m o' = true ∧ n ≠ m

/-- Enough probability laws for the displayed event union bounds. A real
instance can be obtained from a discrete or measurable probability measure. -/
structure Experiment (Ω : Type) where
  prob : (Ω → Prop) → Rat
  nonneg : ∀ E, 0 ≤ prob E
  total : prob (fun _ => True) = 1
  empty : prob (fun _ => False) = 0
  mono : ∀ E F, (∀ ω, E ω → F ω) → prob E ≤ prob F
  union_le : ∀ E F, prob (fun ω => E ω ∨ F ω) ≤ prob E + prob F

structure Game (A Ω : Type) where
  experiment : A → Experiment Ω
  admissible : Nat → A → Prop

/-- Resource closure is a separate proof obligation, not a query-count comment. -/
def ReductionWithin {A B Ω Ξ : Type} (source : Game A Ω) (target : Game B Ξ)
    (reduce : A → B) (budget : Nat → Nat) : Prop :=
  ∀ q a, source.admissible q a → target.admissible (budget q) (reduce a)

/-- The advantage is connected to executions and resource admissibility.
For a ROM instance S itself must be interpreted in the sampled oracle world;
use the more general `Sω` version below. -/
def ComputationalBinding {A Ω : Type} (G : Game A Ω)
    (Sω : Ω → ContentScheme Sym Digest Op LenOp)
    (output : A → Ω → BindingWitness (Sym := Sym) (Digest := Digest)
      (Op := Op) (LenOp := LenOp)) (ε : Nat → Rat) : Prop :=
  ∀ q a, G.admissible q a →
    (G.experiment a).prob (fun ω => BindingWin (Sω ω) (output a ω)) ≤ ε q

/-- Bounds are explicit; unlike List.drop/take alone they do not clamp. -/
def SpanAt (w : List Sym) (i : Nat) (p : List Sym) : Prop :=
  i + p.length ≤ w.length ∧ (w.drop i).take p.length = p

def SubstringAt (c : Digest) (i : Nat) (p w : List Sym) : Prop :=
  S.commit w = c ∧ SpanAt w i p

def OccursIn (c : Digest) (p w : List Sym) : Prop :=
  ∃ i, SubstringAt S c i p w

def MatchesAt {Regex : Type} (accepts : List Sym → Regex → Prop)
    (c : Digest) (i j : Nat) (r : Regex) (w : List Sym) : Prop :=
  S.commit w = c ∧ i ≤ j ∧ j ≤ w.length ∧ accepts ((w.drop i).take (j - i)) r

def FormOK (language : List Sym → Prop) (c : Digest) (w : List Sym) : Prop :=
  S.commit w = c ∧ language w

def Framed {Data : Type} (render : Data → List Sym) (safe : Data → Prop)
    (c : Digest) (w : List Sym) : Prop :=
  S.commit w = c ∧ ∃ d, w = render d ∧ safe d

def AbsentLiteral (c : Digest) (p w : List Sym) : Prop :=
  S.commit w = c ∧ ∀ i, ¬ SpanAt w i p

def AbsentLanguage (language : List Sym → Prop) (w : List Sym) : Prop :=
  ¬ ∃ pre mid post, w = pre ++ mid ++ post ∧ language mid

def AllRecords {Root : Type} (mroot : List Digest → Root) (r : Root)
    (n : Nat) (φ : List Sym → Prop) : Prop :=
  ∃ roots : List Digest, mroot roots = r ∧ roots.length = n ∧
    ∀ c ∈ roots, ∃ w, S.commit w = c ∧ φ w

structure InferenceStatement (Model Context Digest : Type) where
  model : Model
  context : Context
  input : Digest
  output : Digest

def Produced {Model Context : Type}
    (eval : Model → Context → List Sym → List Sym → Prop)
    (s : InferenceStatement Model Context Digest) (input output : List Sym) : Prop :=
  S.commit input = s.input ∧ S.commit output = s.output ∧
    eval s.model s.context input output

/-- The E parameter is chosen before the adversary and its actual experiment.
An outer ∃ E with an efficiency bound supplies a certificate package. -/
def KnowledgeSound {A Ω X Proof Log W : Type} (G : Game A Ω)
    (stmt : A → Ω → X) (proof : A → Ω → Proof) (log : A → Ω → Log)
    (verify : Ω → X → Proof → Bool) (relation : Ω → X → W → Prop)
    (extract : Log → W) (ε : Nat → Rat) : Prop :=
  ∀ q a, G.admissible q a → (G.experiment a).prob (fun ω =>
    verify ω (stmt a ω) (proof a ω) = true ∧
    ¬ relation ω (stmt a ω) (extract (log a ω))) ≤ ε q

def BindsContent {X : Type} (root : X → Digest)
    (relation : X → List Sym → Prop) : Prop :=
  ∀ x w, relation x w → S.commit w = root x

/-- Fixed-experiment conjunction target. Error premises concern extracted words,
not independent experiments. β must be discharged by the concrete reduction,
with its actual query/time overhead, to the BindingWitness game. -/
def ConjunctionBound {Ω : Type} (μ : Experiment Ω)
    (Sω : Ω → ContentScheme Sym Digest Op LenOp)
    (accept₁ accept₂ : Ω → Prop) (root : Ω → Digest)
    (w₁ w₂ : Ω → List Sym) (φ ψ : List Sym → Prop)
    (ε₁ ε₂ β : Rat) : Prop :=
  μ.prob (fun ω => accept₁ ω ∧ ¬ ((Sω ω).commit (w₁ ω) = root ω ∧ φ (w₁ ω))) ≤ ε₁ →
  μ.prob (fun ω => accept₂ ω ∧ ¬ ((Sω ω).commit (w₂ ω) = root ω ∧ ψ (w₂ ω))) ≤ ε₂ →
  μ.prob (fun ω => (Sω ω).commit (w₁ ω) = root ω ∧ (Sω ω).commit (w₂ ω) = root ω ∧
    w₁ ω ≠ w₂ ω) ≤ β →
  μ.prob (fun ω => accept₁ ω ∧ accept₂ ω ∧
    ¬ ((Sω ω).commit (w₁ ω) = root ω ∧ φ (w₁ ω) ∧ ψ (w₁ ω))) ≤ ε₁ + ε₂ + β

/-- A deterministic extraction law: no binding needed when the conclusion is
exactly the existential AllRecords relation and the same explicit root list. -/
def AggregateExtracted {Root : Type} (mroot : List Digest → Root)
    (r : Root) (n : Nat) (φ : List Sym → Prop) (roots : List Digest) : Prop :=
  mroot roots = r → roots.length = n →
  (∀ c ∈ roots, ∃ w, S.commit w = c ∧ φ w) → AllRecords S mroot r n φ

/-- Resource and joint-run bounds for each proof are premises of its probability
version. Replacing sum errors by εengine requires εengine for the final semantic
relation, not merely correct recursive verification of leaf verifiers. -/
def AggregateFailureBound {Ω : Type} (μ : Experiment Ω) (n : Nat)
    (bad : Fin n → Ω → Prop) (aggregateBad : Ω → Prop) (ε : Fin n → Rat)
    : Prop :=
  (∀ ω, aggregateBad ω → ∃ k, bad k ω) →
  (∀ k, μ.prob (bad k) ≤ ε k) → μ.prob aggregateBad ≤ (List.ofFn ε).foldr (· + ·) 0

/-- Valid for a length-preserving language interpretation, including nullable
regexes. A nullable r makes the absent side false for every w, as it should. -/
def PaddedComplement {Regex : Type} (accepts : List Sym → Regex → Prop)
    (padNeg : Regex → Regex) : Prop :=
  ∀ w r, AbsentLanguage (fun mid => accepts mid r) w ↔ accepts w (padNeg r)

/-- Same-word morphism. Mere computability of f is not this equation. -/
def SchemeMorphism {Digest' Op' LenOp' : Type}
    (T : ContentScheme Sym Digest' Op' LenOp') (f : Digest → Digest') : Prop :=
  ∀ w, f (S.commit w) = T.commit w

def TransportWitness {Digest' Op' LenOp' : Type}
    (T : ContentScheme Sym Digest' Op' LenOp') (f : Digest → Digest')
    (φ : List Sym → Prop) : Prop :=
  SchemeMorphism S T f → ∀ c w,
    S.commit w = c ∧ φ w → T.commit w = f c ∧ φ w

/-- Tier one authenticates against an independently supplied committed reference
word; it does not extract a whole word from a few paths. -/
def TierOneRelative {Ω : Type} (μ : Experiment Ω)
    (Sω : Ω → ContentScheme Sym Digest Op LenOp)
    (reference pattern : Ω → List Sym) (root : Ω → Digest)
    (position : Ω → Nat) (accepted : Ω → Prop) (β : Rat) : Prop :=
  μ.prob (fun ω => accepted ω ∧ (Sω ω).commit (reference ω) = root ω ∧
    ¬ SpanAt (reference ω) (position ω) (pattern ω)) ≤ β

/-- No phantom preimage inference is asserted by TierOneRelative. To expose a
whole-word certificate a separate existence/extraction leg is necessary. -/
def ExtractedWordAvailable {Ω : Type} (accepted : Ω → Prop)
    (root : Ω → Digest) (extract : Ω → List Sym) : Prop :=
  ∀ ω, accepted ω → S.commit (extract ω) = root ω

/-- The full typed output bridge event: extracted inference word a, bridge b,
property word d, two commitment schemes; both comparisons can fail separately. -/
def BridgeJoin {Digest' Op' LenOp' : Type}
    (T : ContentScheme Sym Digest' Op' LenOp')
    (a b d : List Sym) (c : Digest) (c' : Digest')
    (produced property : List Sym → Prop) : Prop :=
  S.commit a = c ∧ produced a →
  S.commit b = c ∧ T.commit b = c' →
  T.commit d = c' ∧ property d →
  (produced a ∧ property a) ∨
  BindingWin S (.word a b) ∨ BindingWin T (.word b d)

/-- Input words are the symbols of the extracted trace, not an unrelated word.
The real DFA's nonempty run convention needs a separate empty-word branch. -/
def BoundDfaRelation {Trace : Type} (traceWord : Trace → List Sym)
    (acceptTrace : Trace → Prop) (emptyAccept : Prop)
    (c : Digest) (w : List Sym) : Prop :=
  S.commit w = c ∧
    ((w = [] ∧ emptyAccept) ∨ ∃ t, acceptTrace t ∧ traceWord t = w)

/-- Denotation target: every lane of each recomputed opening root is checked.
No assertion that all distinct honest roots must be refused is made. -/
def AllLaneOpening {Input Trace F : Type}
    (holds : Input → Trace → Prop) (root : Input → Fin 8 → F)
    (recomputed : Trace → Fin 8 → F) : Prop :=
  ∀ s t, holds s t → ∀ lane, root s lane = recomputed t lane

def TamperedLaneRefused {Input Trace F : Type}
    (holds : Input → Trace → Prop) (root : Input → Fin 8 → F)
    (recomputed : Trace → Fin 8 → F) : Prop :=
  AllLaneOpening holds root recomputed →
    ∀ s t, (∃ lane, root s lane ≠ recomputed t lane) → ¬ holds s t

end Astra.CertificateStatements
