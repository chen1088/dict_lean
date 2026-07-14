import DictatorshipTesting.Basic

/-
Direct reverse imports:
- `DictatorshipTesting.AlgebraicProperty.Eq_algebraic_property_RowDict`
- `DictatorshipTesting.BasicFacts`
-/
namespace DictatorshipTesting

variable {α : Type*}

@[simp] theorem pcomp_apply (σ τ : Perm α) (x : α) :
    (σ ∘p τ) x = σ (τ x) := rfl

end DictatorshipTesting
