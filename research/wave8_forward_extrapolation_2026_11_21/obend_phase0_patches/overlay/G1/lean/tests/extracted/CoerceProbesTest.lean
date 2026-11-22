module
/- Teeth for `Obend.Elab.Coerce`, run by the build on the actual checker. -/
public import Obend.Elab.Coerce
public meta import Obend.Elab.Coerce

public section
namespace Obend.Elab.Proofs.CoerceProbes
open Obend.Core.Ty Obend.Core.Check Obend.Core.Bidirectional Obend.Elab.Coerce
open Obend.Core.Proofs.BidirectionalCompleteness
open Obend.Core.Term (Term)

def quantities : List Quantity := [.erased, .affine, .linear, .unrestricted]

/-- η-wrapper probe: `λx. f x` at a `q'` parameter, `f` an unrestricted reusable
`q → Nat` function in the context. -/
def wrapperMeasured (q q' : Quantity) : Bool :=
  (checkAgainst ⟨.lam (.app (.bound 1) (.bound 0)),
      fun path => if path = [] then some ⟨.natural, .natural, q', .reusable⟩ else none, {}⟩
    [⟨.arrow .reusable q .natural .natural, .unrestricted⟩]
    (.arrow .reusable q' .natural .natural)).toBool

-- The measured matrix, row by row. Until `linear` separated from `affine` (2026-11-01),
-- the matrix was [[F,T,T,T],[F,T,T,T],[F,T,T,T],[F,F,F,T]]. Exactly two cells change,
-- (erased, linear) and (affine, linear): a wrapper whose parameter is `linear` hands it to a callee
-- that may drop it, and `argumentAllowed` now refuses a `linear` hypothesis as the argument of a
-- non-`linear` parameter. Every other cell, (linear, affine) among them, is unchanged.
#guard (quantities.map fun q => quantities.map fun q' => wrapperMeasured q q') =
  [[false, true, false, true], [false, true, false, true], [false, true, true, true], [false, false, false, true]]
-- the two changed cells are refused by name: the argument at [0, 1] uses the linear hypothesis 0
#guard (quantities.filter fun q => wrapperMeasured q .linear) = [.linear]
#guard [Quantity.erased, .affine].all fun q =>
  match checkAgainst ⟨.lam (.app (.bound 1) (.bound 0)),
      fun path => if path = [] then some ⟨.natural, .natural, .linear, .reusable⟩ else none, {}⟩
    [⟨.arrow .reusable q .natural .natural, .unrestricted⟩] (.arrow .reusable .linear .natural .natural) with
  | .error (.linearArgumentDropped [0, 1] 0 q') => q' == q
  | _ => false
-- the cells `launders` names are exactly the cells that changed
#guard quantities.all fun q => quantities.all fun q' => launders q q' == (q' == .linear && q != .linear && q != .unrestricted)
-- and `wrapperAllowed` is that matrix
#guard quantities.all fun q => quantities.all fun q' => wrapperMeasured q q' == wrapperAllowed q q'

/-- Multi-field custody source row: a custody handle, a natural, and a once closure. -/
def custodyRow : Ty :=
  .field "handle" (.custody 0) (.field "tag" .natural
    (.field "extra" (.arrow .once .affine .natural .natural) .emptyRow))

def projection (q : Quantity) (kept : List String) : Bool :=
  let target := kept.foldr (fun name row => Ty.field name
    (if name == "handle" then .custody 0 else .natural) row) .emptyRow
  (checkAgainst ⟨.lam (.record (kept.map fun name => (name, .get (.bound 0) name))),
      fun path => if path = [] then some ⟨custodyRow, target, q, .once⟩ else none, {}⟩
    [] (.arrow .once q custodyRow target)).toBool

-- custody-bearing records must be bound `linear` (`mustBeLinear`), and `.get` refuses `linear`
-- projection (dropping siblings), so width projection of `custodyRow` is refused at every quantity
#guard quantities.all fun q => !projection q ["handle"]
#guard quantities.all fun q => !projection q ["tag"]
#guard quantities.all fun q => !projection q ["handle", "tag"]

-- `coerce` agrees: identity on `custodyRow` checks (`linear`), one-field width projection is
-- refused by the checker (`invalidContext` on the `affine` binder), and two-field is `needsSharing`
#guard (coerce {} custodyRow custodyRow).toBool
#guard (match coerce {} custodyRow (.field "handle" (.custody 0) .emptyRow) with
  | .error (.checker (.invalidContext [])) => true | _ => false)
#guard (match coerce {} custodyRow (.field "handle" (.custody 0) (.field "tag" .natural .emptyRow)) with
  | .error (.needsSharing _) => true | _ => false)

-- a shareable seed with an extra member coerces to the row without it
def seedRow : Ty := .field "x" .natural (.field "extra" .boolean .emptyRow)
#guard (coerce {} seedRow (.field "x" .natural .emptyRow)).toBool
#guard (coerce {} seedRow (.field "extra" .boolean (.field "x" .natural .emptyRow))).toBool

-- depth: a nested record member is coerced in place
#guard (coerce {} (.field "p" seedRow .emptyRow) (.field "p" (.field "x" .natural .emptyRow) .emptyRow)).toBool

-- sums widen, payloads coerced inside their arms
#guard (coerce {} (.variant (.field "a" .natural .emptyRow))
  (.variant (.field "a" .natural (.field "b" .boolean .emptyRow)))).toBool
#guard (match coerce {} (.variant (.field "a" .natural (.field "b" .boolean .emptyRow)))
  (.variant (.field "a" .natural .emptyRow)) with
  | .error (.missingLabel "b" _) => true | _ => false)

-- functions: the η-wrapper inside the measured matrix, refusals outside it. Relabelling a `linear`
-- parameter as `affine` launders a once-resource: refused by name (it was emitted before 11-01)
#guard (match coerce {} (.arrow .reusable .affine .natural seedRow)
  (.arrow .reusable .linear .natural (.field "x" .natural .emptyRow)) with
  | .error (.launders .affine .linear) => true | _ => false)
#guard (match coerce {} (.arrow .reusable .erased .natural .natural) (.arrow .reusable .linear .natural .natural) with
  | .error (.launders .erased .linear) => true | _ => false)
-- the converse direction keeps the once-resource in a `linear` slot: emitted and checked
#guard (coerce {} (.arrow .reusable .linear .natural seedRow)
  (.arrow .reusable .affine .natural (.field "x" .natural .emptyRow))).toBool
#guard (coerce {} (.arrow .reusable .affine .natural seedRow)
  (.arrow .reusable .affine .natural (.field "x" .natural .emptyRow))).toBool
-- `linear` to `linear` with a record codomain coercion: the component applied to `f y` is emitted
-- `linear`, and a width coercion projects its `linear` parameter, dropping the other fields, which
-- the projection rule refuses by name (records are multiplicative; checked before 11-01 round 2)
#guard (match coerce {} (.arrow .reusable .linear .natural seedRow)
  (.arrow .reusable .linear .natural (.field "x" .natural .emptyRow)) with
  | .error (.checker (.linearProjected _ 0)) => true | _ => false)
-- a sum codomain coercion keeps the whole payload: `linear` to `linear` is emitted and checked (the
-- case over the `linear` component binds its payload `linear`, used once by the re-injection)
#guard (coerce {} (.arrow .reusable .linear .natural (.variant (.field "a" .natural .emptyRow)))
  (.arrow .reusable .linear .natural (.variant (.field "a" .natural (.field "b" .boolean .emptyRow))))).toBool
-- without the relabelling the same component is `affine`, and the kernel names the drop
#guard (match checkAgainst ⟨.lam (.lam (.app (.lam (.record [("x", .get (.bound 0) "x")])) (.app (.bound 1) (.bound 0)))),
      treeAnnotations (.node (some ⟨.arrow .reusable .linear .natural seedRow,
          .arrow .reusable .linear .natural (.field "x" .natural .emptyRow), .unrestricted, .reusable⟩)
        [.node (some ⟨.natural, .field "x" .natural .emptyRow, .linear, .reusable⟩)
          [.node (some (hint (.arrow .reusable .affine seedRow (.field "x" .natural .emptyRow)) (.field "x" .natural .emptyRow)))
            [.node (some ⟨seedRow, .field "x" .natural .emptyRow, .affine, .reusable⟩)
              [.node (some (hint .emptyRow (.field "x" .natural .emptyRow))) [.node none [.node none []]]],
             .node (some (hint (.arrow .reusable .linear .natural seedRow) seedRow)) [.node none [], .node none []]]]]), {}⟩
    [] (.arrow .reusable .unrestricted (.arrow .reusable .linear .natural seedRow)
      (.arrow .reusable .linear .natural (.field "x" .natural .emptyRow))) with
  | .error (.linearArgumentDropped _ 0 .affine) => true | _ => false)
-- and with a record domain coercion: `d y` projects the `linear` argument, refused by name
#guard (match coerce {} (.arrow .reusable .linear (.field "x" .natural .emptyRow) .natural)
  (.arrow .reusable .linear seedRow .natural) with
  | .error (.checker (.linearProjected _ 0)) => true | _ => false)
-- a domain coercion that drops every field of the `linear` argument is refused at its binder
#guard (match coerce {} (.arrow .reusable .linear .emptyRow .natural)
  (.arrow .reusable .linear seedRow .natural) with
  | .error (.checker (.linearBinderUnused _)) => true | _ => false)
#guard (match coerce {} (.arrow .reusable .unrestricted .natural .natural) (.arrow .reusable .affine .natural .natural) with
  | .error (.quantityNotWrappable .unrestricted .affine) => true | _ => false)
#guard (match coerce {} (.arrow .reusable .affine .natural .natural) (.arrow .reusable .erased .natural .natural) with
  | .error (.quantityNotWrappable .affine .erased) => true | _ => false)
#guard (match coerce {} (.arrow .once .affine .natural .natural) (.arrow .reusable .affine .natural .natural) with
  | .error (.reuseChanged .once .reusable) => true | _ => false)

-- coercions into an alias whose unfolding differs are refused by name (no recursive wrappers)
#guard (match coerce ⟨[(0, .variant (.field "a" .boolean .emptyRow))], [], [], []⟩
    (.variant (.field "a" .natural .emptyRow)) (.variable 0) with
  | .error (.recursive _ _) => true | _ => false)

end Obend.Elab.Proofs.CoerceProbes
end
