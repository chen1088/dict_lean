import DictatorshipTesting.Paper.Aux_HEvenFiniteInduction

/-!
# Finite induction input for Lemma 5.6

The intended proof branches once to even diagrams, applies Lemma 5.5 to the
non-exceptional children, and handles the two level-two odd shapes explicitly.

The statement is phrased only in terms of the concrete finite model in
`Defs.lean`, so proving it should not require representation theory.
-/

namespace DictatorshipTesting

/-- Finite Young-diagram induction behind Lemma 5.6. -/
theorem hOdd_ge_one_sixth_youngDim_of_not_oneRow_not_standard_finite_induction
    (m : ℕ) (hm : 2 ≤ m)
    (lam : YoungDiagram (2 * m + 1))
    (hrow : ¬ IsOneRow lam) (hstd : ¬ IsStandard lam) :
    (1 / 6 : ℝ) * youngDim lam ≤ hOdd m lam := by
  -- TODO: use the one-box branching definition of `hOdd`, then split into the
  -- generic case covered by Lemma 5.5 and the two exceptional shapes
  -- `(2m-1,2)` and `(2m-1,1,1)`.
  sorry

end DictatorshipTesting
