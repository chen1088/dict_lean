import DictatorshipTesting.Paper.Defs.S02_Def2_04_IsImageDictator
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S02_Def2_06_IsDictator`
-/


/-!
Definition file for `IsPreimageDictator`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Preimage dictators: `f π = h (π⁻¹ j)`. -/
def IsPreimageDictator {α : Type*} (f : BoolFn α) : Prop :=
  ∃ j : α, ∃ h : α → Bool, ∀ π : Perm α, f π = h (π.symm j)

end DictatorshipTesting
