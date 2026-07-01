import DictatorshipTesting.Basic

namespace DictatorshipTesting

variable {α : Type*}

@[simp] theorem pcomp_apply (σ τ : Perm α) (x : α) :
    (σ ∘p τ) x = σ (τ x) := rfl

end DictatorshipTesting
