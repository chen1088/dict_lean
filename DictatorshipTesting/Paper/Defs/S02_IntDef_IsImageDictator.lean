import DictatorshipTesting.Paper.Defs.S02_IntDef_BoolFnToReal
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S02_IntDef_IsPreimageDictator`
-/


/-!
Definition file for `IsImageDictator`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Image dictators: `f π = h (π i)`. -/
def IsImageDictator {α : Type*} (f : BoolFn α) : Prop :=
  ∃ i : α, ∃ h : α → Bool, ∀ π : Perm α, f π = h (π i)

end DictatorshipTesting
