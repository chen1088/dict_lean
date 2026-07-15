import DictatorshipTesting.Paper.Defs.S02_IntDef_IsImageDictator
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S02_IntDef_IsDictator`
-/


/-!
Definition file for `IsPreimageDictator`.
-/

noncomputable section

namespace DictatorshipTesting

/-- Preimage dictators: `f π = h (π⁻¹ j)`. -/
def IsPreimageDictator {α : Type*} (f : BoolFn α) : Prop :=
  ∃ j : α, ∃ h : α → Bool, ∀ π : Perm α, f π = h (π.symm j)

end DictatorshipTesting
