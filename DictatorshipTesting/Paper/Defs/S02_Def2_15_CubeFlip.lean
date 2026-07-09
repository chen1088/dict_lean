import DictatorshipTesting.Paper.Defs.S02_Def2_14_CubeChar

/-!
Definition file for `cubeFlip`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Flip one coordinate of a Boolean-cube point. -/
def cubeFlip {m : ℕ} (r : Fin m) (x : Cube m) : Cube m :=
  Function.update x r (!(x r))

end DictatorshipTesting
