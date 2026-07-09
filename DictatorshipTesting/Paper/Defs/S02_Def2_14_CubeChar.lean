import DictatorshipTesting.Paper.Defs.S02_Def2_13_Cube

/-!
Definition file for `cubeChar`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Boolean-cube character indexed by a finite set of coordinates. -/
def cubeChar {m : ℕ} (S : Finset (Fin m)) (x : Cube m) : ℝ :=
  ∏ r ∈ S, if x r then (-1 : ℝ) else 1

end DictatorshipTesting
