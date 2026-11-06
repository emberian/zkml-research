/-
# The model-identity receipt (initiative 13), version 2

A receipt binds, for one checkpoint:
(a) a FlashProve commitment ID (their offline weight commitment, `docs/protocol.md` section 3, R4.11);
(b) the registry v2 root set R over the integers FlashProve commits (`ROOTS-V2.md`), which names the integers node;
(c) an evaluation record, signed by an evaluator key, over (a), (b), the sums digest, the file digest, the
    provenance graph's digest and the evaluated deployment;
(d) the provenance graph: typed nodes (one per role), typed relations between them, each relation carrying who
    vouches for it.

`verify` is the accept decision of the CLI (`Main.lean`); there is no second implementation of it. It is generic
over `Crypto`, so every theorem holds for any hash and any signature scheme; the CLI instantiates SHA-256 and
Ed25519 from `Mir.Crypto`. No theorem assumes a cryptographic property: where one is needed, the conclusion carries
an explicit failure (a binding break of FlashProve's commitment, a SHA-256 collision on named inputs, a soundness
failure of FlashProve's verifier).

Version 2 answers the first cross-model attack (gpt-6-astra, 2026-11-06, `notes/attack-1.md`): roles are unique,
relations are typed and only the two the theorem uses are required, an evaluation names a deployment whose digest
`verify` recomputes from its components (no transfer along "exact" edges), recomputer signatures cover the endpoint
kinds and digests, and the commitment edge is a statement about one run plus FlashProve's binding, not a universal
premise.
-/
namespace Mir

/-- A node: one per role. `digest` is 64 lowercase hex digits. -/
structure Node where
  id : String
  kind : String
  digest : String
deriving Repr, DecidableEq, Inhabited

/-- What an edge asserts, `src` to `dst`.
- `converts`: FlashProve `docs/model.md` section 11 maps the files `src` (file-list digest) to integers whose
  registry v2 root set is `dst`.
- `commits`: `cp_commit` run on the files `src` (with the public seed and configuration the rule names) produced
  commitment ID `dst`.
- `quantizes`: a lossy third-party conversion (bf16 to GGUF). Informational; an evaluation never crosses it.
- `digestOf`: `dst` is a digest computed from `src` (the sums file of the integers). Informational. -/
inductive Rel where
  | converts | commits | quantizes | digestOf
deriving Repr, DecidableEq, Inhabited

def Rel.tag : Rel → String
  | .converts => "converts" | .commits => "commits" | .quantizes => "quantizes" | .digestOf => "digest-of"

/-- Who vouches. `rerunnable`: the receipt names a command a stranger can re-run; `verify` does not run it.
`recomputed`: a named key re-ran it and signed the edge's content (`edgeFieldsOf`). `published`: a third party
published the result. Strict mode accepts only `recomputed` by a key the client trusts, on the required edges. -/
inductive Basis where
  | rerunnable (how : String)
  | recomputed (signer : String) (signature : String)
  | published (source : String)
deriving Repr, DecidableEq, Inhabited

structure Edge where
  src : String
  dst : String
  rel : Rel
  rule : String
  basis : Basis
deriving Repr, DecidableEq, Inhabited

structure Graph where
  nodes : List Node
  edges : List Edge
deriving Repr, DecidableEq, Inhabited

/-- The signed evaluation record. `node` must be the deployment node. `benchmark` and `scores` are free text and
enter the signed fields by hash. -/
structure EvalRecord where
  evaluator : String
  publicKey : String
  node : String
  benchmark : String
  scores : String
  signature : String
deriving Repr, DecidableEq, Inhabited

structure Receipt where
  commitmentId : String
  rootset : String
  wsums : String
  filesDigest : String
  graph : Graph
  eval : EvalRecord
deriving Repr, DecidableEq, Inhabited

/-- `sigOk pk fields sig`: the signature verifies under `pk` on the encoding of `fields` (the CLI: a domain tag, the
count, each field's 32 raw bytes). -/
structure Crypto where
  hash : String → String
  sigOk : String → List String → String → Bool

/-- No key accepts one signature on two different field lists. Not a standard unforgeability game: it is the
property whose violation `swap_needs_forgery` exhibits. With the CLI's fixed-width encoding (tag, count, 32 raw
bytes per field) a violation is a signature valid on two different messages under one key. -/
def OneListPerSignature (c : Crypto) : Prop :=
  ∀ pk sig (l₁ l₂ : List String), c.sigOk pk l₁ sig = true → c.sigOk pk l₂ sig = true → l₁ = l₂

def isHex64 (s : String) : Bool :=
  s.length == 64 && s.all (fun ch => ch.isDigit || ('a' ≤ ch && ch ≤ 'f'))

def textOk (s : String) : Bool := !(s.any (fun ch => ch == '\t' || ch == '\n'))

def basisText : Basis → String
  | .rerunnable h => "rerunnable\t" ++ h
  | .recomputed s _ => "recomputed\t" ++ s
  | .published s => "published\t" ++ s

def basisOk : Basis → Bool
  | .rerunnable h => textOk h
  | .recomputed s _ => textOk s
  | .published s => textOk s

/-- The signed projection of the graph: every node and every edge except recomputer signatures (they sign the
edge's content themselves). -/
def graphText (g : Graph) : String :=
  let ns := g.nodes.map (fun n => "node\t" ++ n.id ++ "\t" ++ n.kind ++ "\t" ++ n.digest ++ "\n")
  let es := g.edges.map (fun e => "edge\t" ++ e.src ++ "\t" ++ e.dst ++ "\t" ++ e.rel.tag ++ "\t" ++ e.rule ++
    "\t" ++ basisText e.basis ++ "\n")
  "mir13/graph/v2\n" ++ String.join ns ++ String.join es

def graphDigest (c : Crypto) (g : Graph) : String := c.hash (graphText g)

/-- The roles: each must be held by exactly one node. -/
def roles : List String :=
  ["gguf-files", "integers", "flashprove-commitment", "deployment",
   "runtime", "tokenizer", "adapter", "system-prompt", "tools"]

/-- The deployment's components. The commitment ID stands for FlashProve's whole configuration (R4.11 hashes
policy, scales and layout); `runtime` names the program that runs the integer model, so an evaluation run on another
runtime (the GGUF in llama.cpp, say) is a different deployment, and signing it as this one is the evaluator's lie. -/
def componentRoles : List String :=
  ["integers", "flashprove-commitment", "runtime", "tokenizer", "adapter", "system-prompt", "tools"]

def nodeById (g : Graph) (i : String) : Option Node := g.nodes.find? (fun n => n.id == i)

def theRole (g : Graph) (k : String) : Option Node :=
  match g.nodes.filter (fun n => n.kind == k) with
  | [n] => some n
  | _ => none

/-- The deployment's digest, recomputed from its components' digests in role order. -/
def deploymentText (g : Graph) : String :=
  "mir13/deployment/v1\n" ++ String.join (componentRoles.map (fun k =>
    k ++ "\t" ++ ((theRole g k).map (·.digest)).getD "" ++ "\n"))

def wellFormed (r : Receipt) : Bool :=
  let g := r.graph
  g.nodes.length ≤ 64 && g.edges.length ≤ 256 &&
  (g.nodes.map (·.id)).eraseDups.length == g.nodes.length &&
  g.nodes.all (fun n => textOk n.id && textOk n.kind && isHex64 n.digest) &&
  g.edges.all (fun e => textOk e.src && textOk e.dst && textOk e.rule && basisOk e.basis &&
    (nodeById g e.src).isSome && (nodeById g e.dst).isSome) &&
  roles.all (fun k => (theRole g k).isSome) &&
  [r.commitmentId, r.rootset, r.wsums, r.filesDigest].all isHex64

/-- The roles carry the receipt's digests, the deployment's digest is its components', and the evaluation names
the deployment. -/
def graphNames (c : Crypto) (r : Receipt) : Bool :=
  let g := r.graph
  (theRole g "flashprove-commitment").map (·.digest) == some r.commitmentId &&
  (theRole g "integers").map (·.digest) == some r.rootset &&
  (theRole g "gguf-files").map (·.digest) == some r.filesDigest &&
  (theRole g "deployment").map (·.digest) == some (c.hash (deploymentText g)) &&
  (theRole g "deployment").map (·.id) == some r.eval.node

/-- An edge `rel` from the role `sk` to the role `dk`. -/
def edgeIs (g : Graph) (rel : Rel) (sk dk : String) (e : Edge) : Bool :=
  e.rel == rel && ((theRole g sk).map (·.id) == some e.src) && ((theRole g dk).map (·.id) == some e.dst)

/-- What a recomputer signs: the relation, both endpoints' kinds and digests, the rule. -/
def edgeFieldsOf (c : Crypto) (rel : Rel) (sk sd dk dd rule : String) : List String :=
  [c.hash ("mir13/edge/v2\t" ++ rel.tag), c.hash sk, sd, c.hash dk, dd, c.hash rule]

/-- Required edge, any basis (default mode) or recomputed by a trusted key whose signature covers the content
(strict mode). -/
def requiredEdge (c : Crypto) (strict : Bool) (recs : List String) (g : Graph) (rel : Rel) (sk dk : String) : Bool :=
  match theRole g sk, theRole g dk with
  | some s, some d => g.edges.any (fun e => edgeIs g rel sk dk e &&
      (!strict || match e.basis with
        | .recomputed k sig => recs.contains k && c.sigOk k (edgeFieldsOf c rel sk s.digest dk d.digest e.rule) sig
        | _ => false))
  | _, _ => false

/-- The fields the evaluator signs. -/
def evalFields (c : Crypto) (r : Receipt) : List String :=
  [c.hash "mir13/eval/v2", r.commitmentId, r.rootset, r.wsums, r.filesDigest, graphDigest c r.graph,
   c.hash r.eval.node, c.hash r.eval.benchmark, c.hash r.eval.scores, c.hash r.eval.evaluator]

/-- The accept decision. `trusted`: evaluator keys the client accepts; `recs`: recomputer keys (strict mode). Both
come from the client, never from the receipt. -/
def verify (c : Crypto) (trusted : List String) (strict : Bool) (recs : List String) (r : Receipt) : Bool :=
  wellFormed r && graphNames c r &&
  requiredEdge c strict recs r.graph .converts "gguf-files" "integers" &&
  requiredEdge c strict recs r.graph .commits "gguf-files" "flashprove-commitment" &&
  trusted.contains r.eval.publicKey &&
  c.sigOk r.eval.publicKey (evalFields c r) r.eval.signature

/-- The decision on a proof: the ID given to FlashProve's verifier must be the receipt's, and it must accept. -/
def accepts (c : Crypto) (trusted : List String) (strict : Bool) (recs : List String) (r : Receipt)
    (fpAccept : String → π → Bool) (cid : String) (p : π) : Bool :=
  verify c trusted strict recs r && cid == r.commitmentId && fpAccept cid p

theorem verify_spec {c : Crypto} {t : List String} {s : Bool} {rc : List String} {r : Receipt}
    (h : verify c t s rc r = true) :
    wellFormed r = true ∧ graphNames c r = true ∧
    requiredEdge c s rc r.graph .converts "gguf-files" "integers" = true ∧
    requiredEdge c s rc r.graph .commits "gguf-files" "flashprove-commitment" = true ∧
    t.contains r.eval.publicKey = true ∧ c.sigOk r.eval.publicKey (evalFields c r) r.eval.signature = true := by
  simp only [verify, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5⟩

/-! ## The world the receipt speaks about

`W`: integer weight sets with their layout (FlashProve's committed integers). `G`: GGUF file sets (their bytes).
`Pf`: FlashProve proofs. -/

structure World (W G Pf : Type) where
  /-- FlashProve `docs/model.md` section 11 at the receipt's e_res: files to integers (deterministic). -/
  conv : G → W
  /-- SHA-256 of `weights.sha256`, the list of the files' SHA-256 (edge E1). -/
  files : G → String
  /-- The registry v2 root set of the integers (`ROOTS-V2.md`). -/
  roots : W → String
  /-- `committed cid x`: the anchor table of commitment `cid` encodes `x`. -/
  committed : String → W → Prop
  /-- `satisfies x p`: the claim of proof `p` (its request's checked tokens under the configuration's policy)
  holds for the integer model `x`. Not "the provider computed it with `x`". -/
  satisfies : W → Pf → Prop
  /-- FlashProve's verifier (`cp_verify`) with the client's configuration files. -/
  fpAccept : String → Pf → Bool

variable {W G Pf : Type}

/-- FlashProve's soundness up to a failure event `bad`. A hypothesis, never an axiom, and unquantified here: `bad`
is whatever their soundness error covers (their bound, not ours); with `bad := True` the theorem is empty, as it
should be when nothing is known of the verifier. -/
def FpSoundUpTo (w : World W G Pf) (bad : Pf → Prop) : Prop :=
  ∀ cid p, w.fpAccept cid p = true → (∃ x, w.committed cid x ∧ w.satisfies x p) ∨ bad p

/-- A break of FlashProve's binding at `cid`: two different integer sets committed under one ID. -/
def BindingBreak (w : World W G Pf) (cid : String) : Prop :=
  ∃ x y, x ≠ y ∧ w.committed cid x ∧ w.committed cid y

/-- Two different file sets with one file-list digest. `G` is the files' bytes, named; `files g` is SHA-256 of
the list of each file's SHA-256, so a witness is a SHA-256 collision at the file layer or at the list layer. The
reduction to two concrete byte strings is not formalised here. -/
def FilesCollision (w : World W G Pf) (f : String) : Prop :=
  ∃ g₁ g₂, g₁ ≠ g₂ ∧ w.files g₁ = f ∧ w.files g₂ = f

/-- What an edge asserts about the world, by relation. -/
def EdgeHolds (w : World W G Pf) : Rel → String → String → Prop
  | .converts, f, rs => ∃ g, w.files g = f ∧ w.roots (w.conv g) = rs
  | .commits, f, cid => ∃ g, w.files g = f ∧ w.committed cid (w.conv g)
  | _, _, _ => True

/-- Edge E2 (our stream; re-runnable by a stranger, gates G11-G13). -/
def StreamTranscript (w : World W G Pf) (r : Receipt) : Prop := EdgeHolds w .converts r.filesDigest r.rootset

/-- Edge E3: what one run of `cp_commit` on these files gives, read semantically: the ID it produced commits to the
§11 integers of those files. Two things are folded in and named here: the run itself (public seed: recomputable on
an H100 with 330 GB; FlashProve published its result) and the committer's correctness (it encodes what it read;
FlashProve proves this of no program, protocol.md section 3). A statement about a run, not about every integer set
under the ID; a hidden-seed commitment needs its own witnessed run, and reproducing this one says nothing of it. -/
def CommitRun (w : World W G Pf) (r : Receipt) : Prop := EdgeHolds w .commits r.filesDigest r.commitmentId

/-- A recomputer key is honest about edges: whatever edge content it signs holds. -/
def HonestRecomputer (c : Crypto) (w : World W G Pf) (k : String) : Prop :=
  ∀ rel sk sd dk dd rule sig, c.sigOk k (edgeFieldsOf c rel sk sd dk dd rule) sig = true → EdgeHolds w rel sd dd

/-- **identity_sound.** A verified receipt and a FlashProve proof accepted against the receipt's commitment ID
imply: the proof's claim holds for integers that §11 converts from files with the receipt's file digest and whose
registry v2 root set is the receipt's, and the trusted evaluator key signed a field list naming that commitment
ID, root set, file digest, the graph and the deployment built from those integers. Or one of three named failures:
FlashProve's verifier failed (`bad p`), FlashProve's binding broke at this ID, or SHA-256 collided on the file list.

Hypotheses and their owners: `FpSoundUpTo` (FlashProve's theorem, with its error event), `StreamTranscript` (our
stream, re-runnable), `CommitRun` (a cp_commit run; FlashProve's published reproduction, or a recomputer).
It does NOT say: that the evaluation was honest or good (the key's owner vouches); that the provider spent the
computation of this model (hollow-LLM's effort gap); that the GGUF behaves like Meta's bf16 model (the quantization
is lossy and the evaluation names the integer deployment); anything a stranger can check about private weights. -/
theorem identity_sound (c : Crypto) (trusted recs : List String) (strict : Bool) (r : Receipt)
    (w : World W G Pf) (bad : Pf → Prop) (cid : String) (p : Pf)
    (hv : verify c trusted strict recs r = true) (hcid : cid = r.commitmentId) (hp : w.fpAccept cid p = true)
    (hfp : FpSoundUpTo w bad) (hs : StreamTranscript w r) (he : CommitRun w r) :
    (∃ x g, w.satisfies x p ∧ x = w.conv g ∧ w.files g = r.filesDigest ∧ w.roots x = r.rootset ∧
      c.sigOk r.eval.publicKey (evalFields c r) r.eval.signature = true ∧
      (evalFields c r).take 5 = [c.hash "mir13/eval/v2", r.commitmentId, r.rootset, r.wsums, r.filesDigest] ∧
      graphNames c r = true ∧ trusted.contains r.eval.publicKey = true) ∨
    bad p ∨ BindingBreak w r.commitmentId ∨ FilesCollision w r.filesDigest := by
  obtain ⟨_, hnames, _, _, htr, hsig⟩ := verify_spec hv
  subst hcid
  rcases hfp _ p hp with ⟨x, hcx, hsx⟩ | hb
  · obtain ⟨g₁, hf₁, hr₁⟩ := hs
    obtain ⟨g₂, hf₂, hc₂⟩ := he
    by_cases hx : x = w.conv g₂
    · by_cases hg : g₁ = g₂
      · left
        subst hg
        exact ⟨x, g₁, hsx, hx, hf₁, by rw [hx]; exact hr₁, hsig, rfl, hnames, htr⟩
      · right; right; right; exact ⟨g₁, g₂, hg, hf₁, hf₂⟩
    · right; right; left; exact ⟨x, w.conv g₂, hx, hcx, hc₂⟩
  · right; left; exact hb

theorem requiredEdge_strict {c : Crypto} {recs : List String} {g : Graph} {rel : Rel} {sk dk : String}
    (h : requiredEdge c true recs g rel sk dk = true) :
    ∃ s d k sig rule, theRole g sk = some s ∧ theRole g dk = some d ∧ recs.contains k = true ∧
      c.sigOk k (edgeFieldsOf c rel sk s.digest dk d.digest rule) sig = true := by
  unfold requiredEdge at h
  split at h
  · rename_i s d hs hd
    obtain ⟨e, _, he⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, Bool.not_true, Bool.false_or] at he
    obtain ⟨_, hb⟩ := he
    split at hb
    · rename_i k sig _
      simp only [Bool.and_eq_true] at hb
      exact ⟨s, d, k, sig, e.rule, hs, hd, hb.1, hb.2⟩
    · simp at hb
  · simp at h

/-- **identity_sound_strict.** In strict mode the two edges come from authenticated recomputer attestations: each
was signed, over relation, endpoint kinds and digests and rule, by a key the client trusts. Trust is not removed;
it moves to `HonestRecomputer`, a premise about every edge such a key signs. -/
theorem identity_sound_strict (c : Crypto) (trusted recs : List String) (r : Receipt)
    (w : World W G Pf) (bad : Pf → Prop) (cid : String) (p : Pf)
    (hv : verify c trusted true recs r = true) (hcid : cid = r.commitmentId) (hp : w.fpAccept cid p = true)
    (hfp : FpSoundUpTo w bad) (hhon : ∀ k, recs.contains k = true → HonestRecomputer c w k) :
    (∃ x g, w.satisfies x p ∧ x = w.conv g ∧ w.files g = r.filesDigest ∧ w.roots x = r.rootset ∧
      c.sigOk r.eval.publicKey (evalFields c r) r.eval.signature = true ∧
      (evalFields c r).take 5 = [c.hash "mir13/eval/v2", r.commitmentId, r.rootset, r.wsums, r.filesDigest] ∧
      graphNames c r = true ∧ trusted.contains r.eval.publicKey = true) ∨
    bad p ∨ BindingBreak w r.commitmentId ∨ FilesCollision w r.filesDigest := by
  obtain ⟨_, hnames, h2, h3, _, _⟩ := verify_spec hv
  have hn := hnames
  simp only [graphNames, Bool.and_eq_true, beq_iff_eq] at hn
  obtain ⟨⟨⟨⟨hcm, hint⟩, hgg⟩, _⟩, _⟩ := hn
  apply identity_sound c trusted recs true r w bad cid p hv hcid hp hfp
  · obtain ⟨s, d, k, sig, rule, hs, hd, hk, hsg⟩ := requiredEdge_strict h2
    have := hhon k hk _ _ _ _ _ _ _ hsg
    rw [hs] at hgg; rw [hd] at hint
    simp only [Option.map_some, Option.some.injEq] at hgg hint
    rw [hgg, hint] at this; exact this
  · obtain ⟨s, d, k, sig, rule, hs, hd, hk, hsg⟩ := requiredEdge_strict h3
    have := hhon k hk _ _ _ _ _ _ _ hsg
    rw [hs] at hgg; rw [hd] at hcm
    simp only [Option.map_some, Option.some.injEq] at hgg hcm
    rw [hgg, hcm] at this; exact this

/-- **hollow_refused.** (1) A proof against any commitment ID other than the receipt's is not accepted under the
receipt, whatever FlashProve's verifier says of it. (2) Under the receipt's own ID, integers whose root set is not
the receipt's (ghost weights, a smaller model, any substitute) can be committed only if FlashProve's binding breaks
there or SHA-256 collides on the file list. Part (2) is where the registry binding works, and it works only for
published weights: for private weights no stranger can re-run `StreamTranscript`. It says nothing about effort. -/
theorem hollow_refused (c : Crypto) (trusted recs : List String) (strict : Bool) (r : Receipt)
    (w : World W G Pf) (hs : StreamTranscript w r) (he : CommitRun w r) :
    (∀ (fpAccept : String → Pf → Bool) (cid : String) (p : Pf), cid ≠ r.commitmentId →
      accepts c trusted strict recs r fpAccept cid p = false) ∧
    (∀ xh, w.committed r.commitmentId xh → w.roots xh ≠ r.rootset →
      BindingBreak w r.commitmentId ∨ FilesCollision w r.filesDigest) := by
  refine ⟨fun fa cid p hne => by simp [accepts, hne], fun xh hcom hhol => ?_⟩
  obtain ⟨g₁, hf₁, hr₁⟩ := hs
  obtain ⟨g₂, hf₂, hc₂⟩ := he
  by_cases hx : xh = w.conv g₂
  · by_cases hg : g₁ = g₂
    · subst hg; exact absurd (by rw [hx]; exact hr₁) hhol
    · exact Or.inr ⟨g₁, g₂, hg, hf₁, hf₂⟩
  · exact Or.inl ⟨xh, w.conv g₂, hx, hcom, hc₂⟩

/-! ## Falsifiers: what an attacker must forge -/

/-- Two verified receipts that differ in a signed field under one key and one signature are a forgery witness. -/
theorem swap_needs_forgery (c : Crypto) (t rc : List String) (s : Bool) (r r' : Receipt)
    (hv : verify c t s rc r = true) (hv' : verify c t s rc r' = true)
    (hk : r'.eval.publicKey = r.eval.publicKey) (hsig : r'.eval.signature = r.eval.signature)
    (hdiff : evalFields c r ≠ evalFields c r') :
    ¬ OneListPerSignature c := by
  intro hinj
  obtain ⟨_, _, _, _, _, h1⟩ := verify_spec hv
  obtain ⟨_, _, _, _, _, h2⟩ := verify_spec hv'
  rw [hk, hsig] at h2
  exact hdiff (hinj _ _ _ _ h1 h2)

/-- Falsifier 1: a swapped commitment ID changes the signed fields. -/
theorem swapped_cid_changes_fields (c : Crypto) (r : Receipt) (x : String) (hx : x ≠ r.commitmentId) :
    evalFields c r ≠ evalFields c { r with commitmentId := x } := by
  intro h; simp [evalFields] at h; exact hx h.symm

/-- Falsifier 2: an evaluation presented for a different checkpoint (another root set) changes the signed fields. -/
theorem other_checkpoint_changes_fields (c : Crypto) (r : Receipt) (x : String) (hx : x ≠ r.rootset) :
    evalFields c r ≠ evalFields c { r with rootset := x } := by
  intro h; simp [evalFields] at h; exact hx h.symm

/-- Falsifier 3: a graph whose signed projection differs (an adapter's digest, a system prompt) changes the signed
fields, or SHA-256 collides on two different graph texts. -/
theorem other_graph_changes_fields (c : Crypto) (r : Receipt) (g : Graph) (hg : graphText g ≠ graphText r.graph) :
    evalFields c r ≠ evalFields c { r with graph := g } ∨
      (graphText g ≠ graphText r.graph ∧ c.hash (graphText g) = c.hash (graphText r.graph)) := by
  by_cases h : c.hash (graphText g) = c.hash (graphText r.graph)
  · exact Or.inr ⟨hg, h⟩
  · left; intro he; simp [evalFields, graphDigest] at he; exact h he.symm

/-- Falsifier 4: a recomputer signature does not survive a change of an endpoint's digest: the signed field lists
differ. -/
theorem edge_digest_changes_fields (c : Crypto) (rel : Rel) (sk sd dk dd rule sd' : String) (h : sd' ≠ sd) :
    edgeFieldsOf c rel sk sd dk dd rule ≠ edgeFieldsOf c rel sk sd' dk dd rule := by
  intro he; simp [edgeFieldsOf] at he; exact h he.symm

end Mir
