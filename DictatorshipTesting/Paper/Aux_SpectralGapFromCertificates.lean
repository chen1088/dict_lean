import DictatorshipTesting.Paper.Aux_CentralizationBridge

/-!
# Spectral gap from certificate inequalities

This is the remaining representation-theoretic boundary after the matching
restriction data, local trace formula, and trace-divided-by-dimension algebra
have been isolated.

Mathematically, this file corresponds to the Young-block spectral
decomposition of `L^2(S_n)`, the Schur-lemma scalarity of the averaged matching
operator on each block, and the identification of `U_1` with the two blocks
indexed by `(n)` and `(n-1,1)`.
-/

noncomputable section

namespace DictatorshipTesting

/-- Even final spectral-decomposition input: if every Young block outside
`U_1` has scalar at least `c`, expressed by the finite certificate inequality,
then the matching spectral gap holds on `S_{2m}`. -/
theorem spectralGapFromEvenCertificates_input
    (m : ℕ) (c : ℝ)
    (hc : 0 ≤ c)
    (hrestrict : MatchingRestrictionEvenInput m)
    (htrace : TraceLocalTruncationEvenInput m)
    (hcert :
      ∀ lam : YoungDiagram (2 * m),
        ¬ IsOneRow lam → ¬ IsStandard lam → c * youngDim lam ≤ hEven m lam) :
    MatchingSpectralGapConstant (2 * m) c := by
  -- TODO: formalize the Young-block decomposition of `L^2(S_{2m})`, the
  -- left/right centrality of the averaged matching operator, and the
  -- identification of the `U1` summand with the `(2m)` and `(2m-1,1)` blocks.
  sorry

/-- Odd final spectral-decomposition input: the analogous bridge on
`S_{2m+1}`. -/
theorem spectralGapFromOddCertificates_input
    (m : ℕ) (c : ℝ)
    (hc : 0 ≤ c)
    (hrestrict : MatchingRestrictionOddInput m)
    (htrace : TraceLocalTruncationOddInput m)
    (hcert :
      ∀ lam : YoungDiagram (2 * m + 1),
        ¬ IsOneRow lam → ¬ IsStandard lam → c * youngDim lam ≤ hOdd m lam) :
    MatchingSpectralGapConstant (2 * m + 1) c := by
  -- TODO: formalize the odd Young-block decomposition, including the ordinary
  -- one-box branching for the unmatched point, and repeat the same spectral
  -- decomposition argument.
  sorry

end DictatorshipTesting
