/- Shape-directed commitment-time extraction for supplied Merkle openings.
The two lookup kinds are separated, and a leaf lookup admits only the fixed
public leaf shape. No hash domain separation or random-oracle law is assumed. -/
import Selvage.EfficientRootOpening
import Selvage.CommitmentFailureReduction

namespace Minidregg.Selvage.ShapeRootExtraction
open EfficientRootOpening
open scoped Classical
noncomputable section
variable {Value Digest : Type} [instDigest : DecidableEq Digest]

/-- Expected node/leaf role is known from depth; a leaf's shape is public. -/
def admits (valid : Value → Prop) (node : Bool) : Query Value Digest → Prop
  | .leaf v => node = false ∧ valid v
  | .node _ _ => node = true

def matchingLog (valid : Value → Prop) (node : Bool) (L : Log Value Digest) : Log Value Digest :=
  L.filter fun e => admits valid node e.1

/-- Only same-role collisions in the currently expected leaf shape are needed.
Known cross-length or leaf/node sponge equalities are not automatically failures. -/
def Collision (valid : Value → Prop) (L : Log Value Digest) : Prop :=
  ResponseCollision (matchingLog valid false L) ∨ ResponseCollision (matchingLog valid true L)

def Bad (valid : Value → Prop) (P L : Log Value Digest) (root : Digest) : Prop :=
  Collision valid L ∨ LateTarget P L root

def preimage (valid : Value → Prop) (node : Bool) (P : Log Value Digest) (d : Digest) :=
  EfficientRootOpening.preimage (matchingLog valid node P) d

/-- A fixed checkpoint yields a global leaf function without searching for
alternative accepted openings or depending on later challenge/query coins. -/
def extractedAt (valid : Value → Prop) (P : Log Value Digest) (default : Value) :
    {k : ℕ} → Digest → (Fin k → Bool) → Value
  | 0,root,_ => match preimage valid false P root with
      | some (.leaf v) => v
      | _ => default
  | k+1,root,address => match preimage valid true P root with
      | some (.node a b) => extractedAt valid P default (if address 0 then b else a)
          (fun i : Fin k => address i.succ)
      | _ => default

omit [DecidableEq Digest] in
/-- Matching retained entries embed into the underlying observed log. -/
theorem mem_matching (valid : Value → Prop) (node : Bool) (L : Log Value Digest)
    (e : Query Value Digest × Digest) :
    e ∈ matchingLog valid node L ↔ e ∈ L ∧ admits valid node e.1 := by
  simp [matchingLog]

/-- Any failure of the narrower extractor is also covered by the earlier
causal collision/late-hit machinery. This implication does not price actual Poseidon. -/
theorem bad_to_unfiltered (valid : Value → Prop) (P L : Log Value Digest) (root : Digest)
    (h : Bad valid P L root) : EfficientRootOpening.Bad P L root := by
  rcases h with (h|h)|h
  · obtain ⟨e,he,e',he',hh,hne⟩ := h
    cases instDigest e.2 e'.2 with
    | isTrue heq =>
      exact Or.inl ⟨e,(mem_matching valid false L e).mp he |>.1,
        e',(mem_matching valid false L e').mp he' |>.1,heq,hne⟩
    | isFalse hne' => exact False.elim (hne' hh)
  · obtain ⟨e,he,e',he',hh,hne⟩ := h
    exact Or.inl ⟨e,(mem_matching valid true L e).mp he |>.1,
      e',(mem_matching valid true L e').mp he' |>.1,hh,hne⟩
  · exact Or.inr h

theorem retained_of_target (valid : Value → Prop) (P L : Log Value Digest) (root : Digest)
    (hgood : ¬Bad valid P L root) (e : Query Value Digest × Digest)
    (he : e ∈ L) (ht : Target P root e.2) : e ∈ P := by
  by_contra hn
  exact hgood (Or.inr ⟨e,he,hn,ht⟩)

theorem preimage_of_good (valid : Value → Prop) (node : Bool)
    (P L : Log Value Digest) (root : Digest)
    (hsub : ∀ e ∈ P,e ∈ L) (hgood : ¬Bad valid P L root)
    (q : Query Value Digest) (d : Digest) (hq : admits valid node q) (he : (q,d) ∈ P) :
    preimage valid node P d = some q := by
  apply EfficientRootOpening.preimage_of_mem
  · exact (mem_matching valid node P (q,d)).mpr ⟨he,hq⟩
  · intro e hem hd
    by_contra hne
    have hm := (mem_matching valid node P e).mp hem
    have hc : ResponseCollision (matchingLog valid node L) :=
      ⟨e,(mem_matching valid node L e).mpr ⟨hsub e hm.1,hm.2⟩,
        (q,d),(mem_matching valid node L (q,d)).mpr ⟨hsub _ he,hq⟩,hd,hne⟩
    cases node
    · exact hgood (Or.inl (Or.inl hc))
    · exact hgood (Or.inl (Or.inr hc))

/-- Supplied-path extraction at its declared checkpoint, checking the actual
expected role at each depth and the fixed public leaf shape at the bottom. -/
theorem extractedAt_eq_of_logged
    (valid : Value → Prop) (H : BinaryMerkle.HashSuite Value Digest)
    (P L : Log Value Digest) (default : Value) (root₀ : Digest)
    (hsub : ∀ e ∈ P,e ∈ L) (hgood : ¬Bad valid P L root₀)
    (v : Value) (hv : valid v) (hleaf : (.leaf v,H.leaf v) ∈ L) :
    ∀ (k : ℕ) (root : Digest) (address : Fin k → Bool) (path : List Digest),
    Target P root₀ root →
    (∀ e ∈ pathLog H (H.leaf v) address path,e ∈ L) →
    BinaryMerkle.recompute H (H.leaf v) address path = some root →
    extractedAt valid P default root address = v := by
  intro k
  induction k with
  | zero =>
      intro root address path htarget hnodes hacc
      cases path with
      | cons a as => simp [BinaryMerkle.recompute] at hacc
      | nil =>
          have heq : H.leaf v = root := by simpa [BinaryMerkle.recompute] using hacc
          have hp := retained_of_target valid P L root₀ hgood
            (.leaf v,H.leaf v) hleaf (by simpa [heq] using htarget)
          have hf := preimage_of_good valid false P L root₀ hsub hgood (.leaf v) (H.leaf v)
            (by simp [admits,hv]) hp
          simp [extractedAt,←heq,hf]
  | succ k ih =>
      intro root address path htarget hnodes hacc
      cases path with
      | nil => simp [BinaryMerkle.recompute] at hacc
      | cons sibling rest =>
          obtain ⟨child,hchild,hroot⟩ :=
            (BinaryMerkle.recompute_cons_some_iff H (H.leaf v) sibling address rest root).mp hacc
          cases hbit : address 0 with
          | false =>
              have hr : H.node child sibling = root := by simpa [hbit] using hroot
              have hm : (.node child sibling,H.node child sibling) ∈ L :=
                hnodes _ (by simp [pathLog,hchild,hbit,evaluate])
              have hp := retained_of_target valid P L root₀ hgood
                (.node child sibling,H.node child sibling) hm (by simpa [hr] using htarget)
              have hf := preimage_of_good valid true P L root₀ hsub hgood
                (.node child sibling) (H.node child sibling) (by simp [admits]) hp
              have ht : Target P root₀ child :=
                Or.inr ⟨(.node child sibling,H.node child sibling),hp,by simp [children]⟩
              have hn : ∀ e ∈ pathLog H (H.leaf v) (fun i => address i.succ) rest,e ∈ L := by
                intro e he
                exact hnodes e (by simp [pathLog,hchild,hbit,he])
              have hi := ih child (fun i => address i.succ) rest ht hn hchild
              simpa [extractedAt,←hr,hf,hbit] using hi
          | true =>
              have hr : H.node sibling child = root := by simpa [hbit] using hroot
              have hm : (.node sibling child,H.node sibling child) ∈ L :=
                hnodes _ (by simp [pathLog,hchild,hbit,evaluate])
              have hp := retained_of_target valid P L root₀ hgood
                (.node sibling child,H.node sibling child) hm (by simpa [hr] using htarget)
              have hf := preimage_of_good valid true P L root₀ hsub hgood
                (.node sibling child) (H.node sibling child) (by simp [admits]) hp
              have ht : Target P root₀ child :=
                Or.inr ⟨(.node sibling child,H.node sibling child),hp,by simp [children]⟩
              have hn : ∀ e ∈ pathLog H (H.leaf v) (fun i => address i.succ) rest,e ∈ L := by
                intro e he
                exact hnodes e (by simp [pathLog,hchild,hbit,he])
              have hi := ih child (fun i => address i.succ) rest ht hn hchild
              simpa [extractedAt,←hr,hf,hbit] using hi

end
end Minidregg.Selvage.ShapeRootExtraction

/-- info: 'Minidregg.Selvage.ShapeRootExtraction.mem_matching' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ShapeRootExtraction.mem_matching

/-- info: 'Minidregg.Selvage.ShapeRootExtraction.bad_to_unfiltered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ShapeRootExtraction.bad_to_unfiltered

/-- info: 'Minidregg.Selvage.ShapeRootExtraction.retained_of_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ShapeRootExtraction.retained_of_target

/-- info: 'Minidregg.Selvage.ShapeRootExtraction.preimage_of_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ShapeRootExtraction.preimage_of_good

/-- info: 'Minidregg.Selvage.ShapeRootExtraction.extractedAt_eq_of_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ShapeRootExtraction.extractedAt_eq_of_logged

