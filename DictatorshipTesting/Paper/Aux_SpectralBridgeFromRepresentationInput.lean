import DictatorshipTesting.Paper.Aux_CentralizationOverMatchings

/-!
# Spectral bridge from representation data

This file is the remaining representation-theoretic boundary for Section 5.
The preceding files isolate the restriction-count input, the one-block trace
formula, and the trace-divided-by-dimension algebra.  What remains here is the
unformalized Young-block decomposition of `L^2(S_n)` and the use of Schur's
lemma to turn the block scalar lower bounds into the global matching spectral
gap.
-/

noncomputable section

namespace DictatorshipTesting

/-- Even spectral bridge after the Specht/Pieri restriction data, the trace
formula, and centralization over matchings. -/
theorem matchingSpectralGap_of_even_young_certificate_input
    (m : ℕ) (c : ℝ)
    (hc : 0 ≤ c)
    (hrestrict : MatchingSubgroupRestrictionEvenInput m)
    (htrace : LocalTruncationTraceEvenInput m)
    (hcert :
      ∀ lam : YoungDiagram (2 * m),
        ¬ IsOneRow lam → ¬ IsStandard lam → c * youngDim lam ≤ hEven m lam) :
    MatchingSpectralGapConstant (2 * m) c := by
  -- TODO: formalize the Young-block decomposition of `L^2(S_{2m})`, prove that
  -- the averaged operator is scalar on each block by Schur's lemma, and combine
  -- the resulting block scalar bounds with the orthogonal decomposition of
  -- `U1`.
  sorry

/-- Odd spectral bridge after the Specht/Pieri restriction data, the trace
formula, and centralization over matchings. -/
theorem matchingSpectralGap_of_odd_young_certificate_input
    (m : ℕ) (c : ℝ)
    (hc : 0 ≤ c)
    (hrestrict : MatchingSubgroupRestrictionOddInput m)
    (htrace : LocalTruncationTraceOddInput m)
    (hcert :
      ∀ lam : YoungDiagram (2 * m + 1),
        ¬ IsOneRow lam → ¬ IsStandard lam → c * youngDim lam ≤ hOdd m lam) :
    MatchingSpectralGapConstant (2 * m + 1) c := by
  -- TODO: formalize the odd Young-block decomposition and the one-box
  -- branching step for the unmatched point, then repeat the even spectral
  -- bridge.
  sorry

end DictatorshipTesting
