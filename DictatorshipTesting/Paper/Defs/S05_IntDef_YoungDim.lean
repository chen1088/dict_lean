import DictatorshipTesting.Paper.Defs.S05_IntDef_YoungDimNat
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S05_IntDef_IsOneRow`
- `DictatorshipTesting.Paper.Defs.S05_IntDef_MatchingRestrictionEvenInput`
- `DictatorshipTesting.Paper.Defs.S05_IntDef_MatchingRestrictionOddInput`
-/


/-!
Definition file for `youngDim`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Dimension of the Specht module indexed by a Young diagram, via the hook
length formula. -/
def youngDim {n : ℕ} (lam : YoungDiagram n) : ℝ :=
  youngDimNat lam

end DictatorshipTesting
