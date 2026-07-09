import DictatorshipTesting.Paper.Defs.S05_IntDef_YoungDimNat

/-!
Definition file for `youngDim`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Dimension of the Specht module indexed by a Young diagram, via the hook
length formula. -/
def youngDim {n : ℕ} (lam : YoungDiagram n) : ℝ :=
  youngDimNat lam

end DictatorshipTesting
