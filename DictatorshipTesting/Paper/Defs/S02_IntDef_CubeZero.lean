import DictatorshipTesting.Paper.Defs.S02_IntDef_CubeXor
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S02_IntDef_CubeDelta`
- `DictatorshipTesting.Paper.S02_Int_CubeCharXor`
-/


/-!
Definition file for `cubeZero`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- The zero point of the Boolean cube. -/
def cubeZero (m : ℕ) : Cube m :=
  fun _ => false

end DictatorshipTesting
