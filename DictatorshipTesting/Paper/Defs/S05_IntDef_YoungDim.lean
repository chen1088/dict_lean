import DictatorshipTesting.Paper.Defs.S05_IntDef_YoungDimNat
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S05_Def5_18_MatchingRestrictionEvenInput`
- `DictatorshipTesting.Paper.Defs.S05_Def5_19_MatchingRestrictionOddInput`
- `DictatorshipTesting.Paper.Defs.S05_IntDef_IsOneRow`
-/


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
