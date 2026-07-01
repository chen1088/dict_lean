import DictatorshipTesting.Paper.Aux_SpectralGapFromCertificates

/-!
# Spectral bridge from representation data

Compatibility names for the final spectral-decomposition input.  New code
should import `Aux_SpectralGapFromCertificates`.
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
  exact spectralGapFromEvenCertificates_input m c hc hrestrict htrace hcert

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
  exact spectralGapFromOddCertificates_input m c hc hrestrict htrace hcert

end DictatorshipTesting
