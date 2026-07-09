import DictatorshipTesting.Paper.S05_IntDef_IsStandard

/-!
Definition file for `IsYoungSubdiagram`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- `mu` is contained in `lam` as a Young diagram. -/
def IsYoungSubdiagram {n k : ℕ} (mu : YoungDiagram k) (lam : YoungDiagram n) : Prop :=
  ∀ i : Fin n, youngRow mu i ≤ youngRow lam i

end DictatorshipTesting
