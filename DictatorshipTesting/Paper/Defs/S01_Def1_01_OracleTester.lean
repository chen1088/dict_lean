import DictatorshipTesting.Paper.Defs.S02_Def2_08_DistToDictators
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S02_Def2_09_OneCosetReal`
- `DictatorshipTesting.Paper.S01_Thm1_01_MainIntro`
-/


/-!
Definition file for `OracleTester`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- A minimal interface for the tester promised by Theorem 1.1. -/
structure OracleTester (α : Type*) [Fintype α] [DecidableEq α] where
  queryCount : ℕ
  nonadaptive : Prop
  oneSided : Prop
  accepts : BoolFn α → Prop
  rejectsWithProbabilityAtLeast : BoolFn α → ℝ → Prop

end DictatorshipTesting
