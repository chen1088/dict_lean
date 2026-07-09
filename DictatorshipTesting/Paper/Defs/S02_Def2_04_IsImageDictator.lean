import DictatorshipTesting.Paper.Defs.S02_Def2_03_BoolFnToReal

/-!
Definition file for `IsImageDictator`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Image dictators: `f π = h (π i)`. -/
def IsImageDictator {α : Type*} (f : BoolFn α) : Prop :=
  ∃ i : α, ∃ h : α → Bool, ∀ π : Perm α, f π = h (π i)

end DictatorshipTesting
