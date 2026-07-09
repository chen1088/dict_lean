import DictatorshipTesting.Basic

/-!
Definition file for `BoolFn`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Boolean functions on a symmetric group. -/
abbrev BoolFn (α : Type*) := Perm α → Bool

end DictatorshipTesting
