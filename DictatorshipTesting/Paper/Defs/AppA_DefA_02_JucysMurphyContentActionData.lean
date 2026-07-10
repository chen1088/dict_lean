import DictatorshipTesting.Paper.Defs.AppA_DefA_01_YoungOrthogonalActionData

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.AppA_ThmA_02_JucysMurphyContentSpectrum`
- `DictatorshipTesting.Paper.Defs.S05_Def5_28_GroupAlgebraAction`
-/

/-!
Appendix A interface definition for Theorem A.2.

This file defines the actual Jucys--Murphy coefficient element and records only
its represented action as the explicit diagonal content operator.  It contains
no matching trace, scalarity, or block-energy fields.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- The group-algebra coefficient function of
`J_a = sum_{i < a} (i,a)` in the symmetric group. -/
def appA_jucysMurphyElement {N : Nat} (a : Fin N) :
    GroupAlgebraElement (Perm (Fin N)) :=
  fun g =>
    ∑ i ∈ (Finset.univ.filter fun i : Fin N => i < a),
      if g = Equiv.swap i a then (1 : Real) else 0

/-- Faithful Lean data for Appendix A.2, tied to a fixed A.1 action: each
actual Jucys--Murphy element acts as the explicit diagonal content operator. -/
structure JucysMurphyContentActionData {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam) where
  rho_content :
    forall a : Fin (n + 1), forall f : TableauSpace lam,
      (∑ g : Perm (Fin (n + 1)),
        appA_jucysMurphyElement a g • action.rep.rho g f) =
          jucysMurphyDiagonalOperator a f

end DictatorshipTesting
