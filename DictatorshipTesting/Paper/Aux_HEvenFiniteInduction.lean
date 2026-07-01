import DictatorshipTesting.Paper.Aux_ZBoundFiniteInduction

/-!
# Finite induction input for Lemma 5.5

The intended proof uses Lemma 5.4, the `hEven` recurrence, the dimension
recursion, and the exceptional level-two Young diagrams from Section 5.

This is deliberately not bundled into the representation-theoretic bridge:
after Lemma 5.2, the paper's remaining work is finite Young-diagram arithmetic.
-/

namespace DictatorshipTesting

/-- Finite Young-diagram induction behind Lemma 5.5. -/
theorem hEven_ge_one_fifth_youngDim_of_not_oneRow_not_standard_finite_induction
    (m : ℕ) (hm : 2 ≤ m)
    (lam : YoungDiagram (2 * m))
    (hrow : ¬ IsOneRow lam) (hstd : ¬ IsStandard lam) :
    (1 / 5 : ℝ) * youngDim lam ≤ hEven m lam := by
  -- TODO: prove the induction from the paper:
  --   * base case `m = 2` by enumerating the three nontrivial shapes;
  --   * generic step from horizontal children and Lemma 5.4 for vertical
  --     children;
  --   * explicit checks for `(2m-2,2)`, `(2m-2,1,1)`, `(2m-3,3)`, and
  --     `(2m-3,2,1)`.
  sorry

end DictatorshipTesting
