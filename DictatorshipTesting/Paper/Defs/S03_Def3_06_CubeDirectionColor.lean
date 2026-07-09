import DictatorshipTesting.Paper.Defs.S03_Def3_05_MatchingCubeRestriction
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S03_Def3_07_CubeColorU`
-/


/-!
Definition file for `CubeDirectionColor`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- The three edge colors used by the square test, encoded as `0`, `1`, `2`. -/
abbrev CubeDirectionColor (m : ℕ) :=
  Fin m → Fin 3

end DictatorshipTesting
