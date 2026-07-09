import DictatorshipTesting.Paper.S02_Def2_18_CubeXor

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
