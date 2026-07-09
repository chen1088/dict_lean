import DictatorshipTesting.Paper.Defs.S01_Def1_01_OracleTester
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S02_Def2_10_U1`
-/


/-!
Definition file for `oneCosetReal`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Real indicator of the one-coset `T_{ij}`. -/
def oneCosetReal {α : Type*} [DecidableEq α] (i j : α) : Perm α → ℝ :=
  fun π => if π i = j then 1 else 0

end DictatorshipTesting
