import DictatorshipTesting.Basic
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S02_IntDef_BoolToReal`
-/


/-!
Definition file for `BoolFn`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Boolean functions on a symmetric group. -/
abbrev BoolFn (α : Type*) := Perm α → Bool

end DictatorshipTesting
