import DictatorshipTesting.Paper.Defs.S02_Def2_18_CubeXor
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S02_Def2_20_CubeDelta`
- `DictatorshipTesting.Paper.S02_Int_CubeCharXor`
-/


/-!
Definition file for `cubeZero`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- The zero point of the Boolean cube. -/
def cubeZero (m : ℕ) : Cube m :=
  fun _ => false

end DictatorshipTesting
