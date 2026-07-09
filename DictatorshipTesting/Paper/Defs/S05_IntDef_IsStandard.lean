import DictatorshipTesting.Paper.Defs.S05_IntDef_IsOneRow

/-!
Definition file for `IsStandard`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- The standard Young diagram `(n-1,1)`. -/
def IsStandard {n : ℕ} (lam : YoungDiagram n) : Prop :=
  2 ≤ n ∧ youngRow lam 0 = n - 1 ∧ youngRow lam 1 = 1

end DictatorshipTesting
