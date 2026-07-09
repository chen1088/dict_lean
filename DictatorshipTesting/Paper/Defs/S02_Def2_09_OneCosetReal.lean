import DictatorshipTesting.Paper.Defs.S01_Def1_01_OracleTester

/-!
Definition file for `oneCosetReal`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Real indicator of the one-coset `T_{ij}`. -/
def oneCosetReal {α : Type*} [DecidableEq α] (i j : α) : Perm α → ℝ :=
  fun π => if π i = j then 1 else 0

end DictatorshipTesting
