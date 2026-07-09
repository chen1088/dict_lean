import DictatorshipTesting.Paper.Defs.S05_IntDef_IsVerticalTwoStripChild

/-!
Definition file for `IsOneBoxChild`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- `lam / mu` consists of one removable box. -/
def IsOneBoxChild {n k : ℕ} (lam : YoungDiagram n) (mu : YoungDiagram k) : Prop :=
  k + 1 = n ∧ IsYoungSubdiagram mu lam

end DictatorshipTesting
