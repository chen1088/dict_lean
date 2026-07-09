import DictatorshipTesting.Paper.Defs.S03_Def3_07_CubeColorU
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S03_Def3_09_MatchingTrialDelta`
-/


/-!
Definition file for `cubeColorV`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- The `B` direction encoded by a square-test coloring. -/
def cubeColorV {m : ℕ} (c : CubeDirectionColor m) : Cube m :=
  fun r => decide (c r = (2 : Fin 3))

end DictatorshipTesting
