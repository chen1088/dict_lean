import DictatorshipTesting.Basic
/-
Direct reverse imports: none.
-/


/-!
Definition file for `BoolFn`.
-/

noncomputable section

namespace DictatorshipTesting

/-- Boolean functions on a symmetric group. -/
abbrev BoolFn (α : Type*) := Perm α → Bool

end DictatorshipTesting
