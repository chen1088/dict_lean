import DictatorshipTesting.Paper.Aux_Def_IsYoungSubdiagram

/-!
Definition file for `IsHorizontalTwoStripChild`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- `lam / mu` is a horizontal two-strip. -/
def IsHorizontalTwoStripChild {n k : ℕ} (lam : YoungDiagram n)
    (mu : YoungDiagram k) : Prop :=
  k + 2 = n ∧
    IsYoungSubdiagram mu lam ∧
      ∀ i : Fin n, youngRow lam ((i : ℕ) + 1) ≤ youngRow mu i

end DictatorshipTesting
