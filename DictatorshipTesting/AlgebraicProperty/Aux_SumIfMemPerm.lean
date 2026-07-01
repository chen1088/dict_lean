import DictatorshipTesting.Basic

/-!
# Reindexing lemma for row dictators

This file contains the finite-sum/bijection step used in
`algebraic_property_rowDict`.
-/

open scoped BigOperators

namespace DictatorshipTesting

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Reindexing lemma behind `eq:algebraic_property`.

Informally:

  `∑_k 1[e k ∈ J] g k = ∑_{j∈J} g (e⁻¹ j)`.

This is the exact finite-sum/bijection step that turns the right-hand side of
the paper's identity into the left-hand side.
-/
lemma sum_if_mem_perm
    (e : Perm α) (J : Finset α) (g : α → ℕ) :
    (∑ k : α, (if e k ∈ J then g k else 0)) =
      ∑ j ∈ J, g (e.symm j) := by
  classical
  calc
    (∑ k : α, (if e k ∈ J then g k else 0))
        = ∑ k ∈ (Finset.univ.filter fun k => e k ∈ J), g k := by
            exact (Finset.sum_filter (s := Finset.univ)
              (p := fun k => e k ∈ J) (f := g)).symm
    _ = ∑ j ∈ J, g (e.symm j) := by
        refine Finset.sum_bij (fun k _ => e k) ?maps_to ?injective ?surjective ?values
        · intro k hk
          exact (Finset.mem_filter.mp hk).2
        · intro a _ b _ h
          exact e.injective h
        · intro j hj
          refine ⟨e.symm j, ?_, ?_⟩
          · simp [hj]
          · simp
        · intro k hk
          simp

end DictatorshipTesting
