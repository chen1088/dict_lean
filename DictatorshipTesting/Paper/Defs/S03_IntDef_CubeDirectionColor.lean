import DictatorshipTesting.Paper.Defs.S03_IntDef_MatchingCubeRestriction
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S03_IntDef_CubeColorU`
-/


/-!
Definition file for `CubeDirectionColor`.
-/

noncomputable section

namespace DictatorshipTesting

/-- The three edge colors used by the square test, encoded as `0`, `1`, `2`. -/
abbrev CubeDirectionColor (m : ℕ) :=
  Fin m → Fin 3

end DictatorshipTesting
