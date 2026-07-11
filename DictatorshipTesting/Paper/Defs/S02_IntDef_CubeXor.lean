import DictatorshipTesting.Paper.Defs.S02_IntDef_CubeFourierCoeff
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S02_IntDef_CubeZero`
- `DictatorshipTesting.Paper.S02_Int_CubeCharXor`
-/


/-!
Definition file for `cubeXor`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Coordinatewise addition on the Boolean cube, written as xor. -/
def cubeXor {m : ℕ} (x y : Cube m) : Cube m :=
  fun r => x r ^^ y r

end DictatorshipTesting
