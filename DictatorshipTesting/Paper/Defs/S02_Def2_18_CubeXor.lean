import DictatorshipTesting.Paper.Defs.S02_Def2_17_CubeFourierCoeff

/-!
Definition file for `cubeXor`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Coordinatewise addition on the Boolean cube, written as xor. -/
def cubeXor {m : ℕ} (x y : Cube m) : Cube m :=
  fun r => x r ^^ y r

end DictatorshipTesting
