import DictatorshipTesting.Paper.S02_Def2_12_L2DistSqToU1

/-!
Definition file for `Cube`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Boolean cube `{0,1}ᵐ`. -/
abbrev Cube (m : ℕ) := Fin m → Bool

end DictatorshipTesting
