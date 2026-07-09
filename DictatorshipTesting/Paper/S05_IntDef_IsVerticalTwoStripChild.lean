import DictatorshipTesting.Paper.S05_IntDef_IsHorizontalTwoStripChild

/-!
Definition file for `IsVerticalTwoStripChild`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- `lam / mu` is a vertical two-strip. -/
def IsVerticalTwoStripChild {n k : ℕ} (lam : YoungDiagram n)
    (mu : YoungDiagram k) : Prop :=
  k + 2 = n ∧
    IsYoungSubdiagram mu lam ∧
      ∀ i : Fin n, youngRow lam i ≤ youngRow mu i + 1

end DictatorshipTesting
