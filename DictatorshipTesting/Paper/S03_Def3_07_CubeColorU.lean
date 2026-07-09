import DictatorshipTesting.Paper.S03_Def3_06_CubeDirectionColor

/-!
Definition file for `cubeColorU`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- The `A` direction encoded by a square-test coloring. -/
def cubeColorU {m : ℕ} (c : CubeDirectionColor m) : Cube m :=
  fun r => decide (c r = (1 : Fin 3))

end DictatorshipTesting
