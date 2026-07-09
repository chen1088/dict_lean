import DictatorshipTesting.Paper.Defs.S02_Def2_04_IsImageDictator

/-!
Definition file for `IsPreimageDictator`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Preimage dictators: `f π = h (π⁻¹ j)`. -/
def IsPreimageDictator {α : Type*} (f : BoolFn α) : Prop :=
  ∃ j : α, ∃ h : α → Bool, ∀ π : Perm α, f π = h (π.symm j)

end DictatorshipTesting
