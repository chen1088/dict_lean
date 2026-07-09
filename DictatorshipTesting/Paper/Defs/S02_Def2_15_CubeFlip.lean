import DictatorshipTesting.Paper.Defs.S02_Def2_14_CubeChar
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S02_Def2_16_CubeExpectation`
- `DictatorshipTesting.Paper.S02_Int_CubeCharFlip`
- `DictatorshipTesting.Paper.S02_Int_CubeFlipInvolutive`
-/


/-!
Definition file for `cubeFlip`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Flip one coordinate of a Boolean-cube point. -/
def cubeFlip {m : ℕ} (r : Fin m) (x : Cube m) : Cube m :=
  Function.update x r (!(x r))

end DictatorshipTesting
