import DictatorshipTesting.Paper.Defs.S02_Def2_13_Cube
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S02_Def2_15_CubeFlip`
- `DictatorshipTesting.Paper.Defs.S05_Def5_15_MatchingCharacters`
- `DictatorshipTesting.Paper.S02_Int_CubeCharMulSelf`
-/


/-!
Definition file for `cubeChar`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Boolean-cube character indexed by a finite set of coordinates. -/
def cubeChar {m : ℕ} (S : Finset (Fin m)) (x : Cube m) : ℝ :=
  ∏ r ∈ S, if x r then (-1 : ℝ) else 1

end DictatorshipTesting
