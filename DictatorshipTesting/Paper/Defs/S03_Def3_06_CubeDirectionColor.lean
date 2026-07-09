import DictatorshipTesting.Paper.Defs.S03_Def3_05_MatchingCubeRestriction

/-!
Definition file for `CubeDirectionColor`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- The three edge colors used by the square test, encoded as `0`, `1`, `2`. -/
abbrev CubeDirectionColor (m : ℕ) :=
  Fin m → Fin 3

end DictatorshipTesting
