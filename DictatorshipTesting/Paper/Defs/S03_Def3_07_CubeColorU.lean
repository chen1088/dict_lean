import DictatorshipTesting.Paper.Defs.S03_Def3_06_CubeDirectionColor
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S03_Def3_08_CubeColorV`
-/


/-!
Definition file for `cubeColorU`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- The `A` direction encoded by a square-test coloring. -/
def cubeColorU {m : ℕ} (c : CubeDirectionColor m) : Cube m :=
  fun r => decide (c r = (1 : Fin 3))

end DictatorshipTesting
