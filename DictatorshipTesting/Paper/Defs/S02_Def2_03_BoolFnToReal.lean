import DictatorshipTesting.Paper.Defs.S02_Def2_02_BoolToReal

/-!
Definition file for `boolFnToReal`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- View a Boolean function as a real-valued `{0,1}` function. -/
def boolFnToReal {α : Type*} (f : BoolFn α) : Perm α → ℝ :=
  fun π => boolToReal (f π)

end DictatorshipTesting
