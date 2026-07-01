import DictatorshipTesting.Paper.Defs

/-!
# Auxiliary facts for products of permutations

These lemmas support the matching-cube completeness proof.
-/

namespace DictatorshipTesting

/-- If every permutation in a list fixes `a`, then the list product fixes `a`. -/
theorem list_perm_prod_apply_eq_of_forall_mem_eq {α : Type*}
    (l : List (Perm α)) (a : α)
    (h : ∀ σ ∈ l, σ a = a) :
    l.prod a = a := by
  induction l with
  | nil =>
      simp
  | cons σ l ih =>
      have htail : l.prod a = a := by
        apply ih
        intro τ hτ
        exact h τ (by simp [hτ])
      have hhead : σ a = a := h σ (by simp)
      simp [List.prod_cons, Equiv.Perm.mul_apply, htail, hhead]

end DictatorshipTesting
