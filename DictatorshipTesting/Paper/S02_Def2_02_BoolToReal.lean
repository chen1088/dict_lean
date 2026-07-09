import DictatorshipTesting.Paper.S02_Def2_01_BoolFn

/-!
Definition file for `boolToReal`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Coerce a Boolean bit to the paper's `{0,1}` real-valued convention. -/
def boolToReal (b : Bool) : ℝ :=
  if b then 1 else 0

end DictatorshipTesting
