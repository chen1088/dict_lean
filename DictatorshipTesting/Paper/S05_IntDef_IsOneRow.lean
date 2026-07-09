import DictatorshipTesting.Paper.S05_IntDef_YoungDim

/-!
Definition file for `IsOneRow`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- The one-row Young diagram. -/
def IsOneRow {n : ℕ} (lam : YoungDiagram n) : Prop :=
  youngRow lam 0 = n

end DictatorshipTesting
