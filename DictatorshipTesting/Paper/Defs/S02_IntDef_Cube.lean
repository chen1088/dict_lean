import DictatorshipTesting.Paper.Defs.S02_IntDef_L2DistSqToU1
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S02_IntDef_CubeChar`
-/


/-!
Definition file for `Cube`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Boolean cube `{0,1}ᵐ`. -/
abbrev Cube (m : ℕ) := Fin m → Bool

end DictatorshipTesting
