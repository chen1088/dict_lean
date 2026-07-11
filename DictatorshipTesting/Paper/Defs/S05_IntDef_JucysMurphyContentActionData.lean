import DictatorshipTesting.Paper.Defs.S05_IntDef_YoungOrthogonalActionData

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S05_Def5_12b_GroupAlgebraAction`
- `DictatorshipTesting.Paper.S05_Int_JucysMurphyContentAction`
-/

/-!
Section 5 interface definition for Theorem Theorem 5.5.

This file defines the actual Jucys--Murphy coefficient element and records only
its represented action as the explicit diagonal content operator.  It contains
no matching trace, scalarity, or block-energy fields.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- The group-algebra coefficient function of
`J_a = sum_{i < a} (i,a)` in the symmetric group. -/
def s05_jucysMurphyElement {N : Nat} (a : Fin N) :
    GroupAlgebraElement (Perm (Fin N)) :=
  fun g =>
    ∑ i ∈ (Finset.univ.filter fun i : Fin N => i < a),
      if g = Equiv.swap i a then (1 : Real) else 0

/-- Faithful Lean data for Section 5.2, tied to a fixed Theorem 5.3 action: each
actual Jucys--Murphy element acts as the explicit diagonal content operator. -/
structure JucysMurphyContentActionData {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam) where
  rho_content :
    forall a : Fin (n + 1), forall f : TableauSpace lam,
      (∑ g : Perm (Fin (n + 1)),
        s05_jucysMurphyElement a g • action.rep.rho g f) =
          jucysMurphyDiagonalOperator a f

end DictatorshipTesting
