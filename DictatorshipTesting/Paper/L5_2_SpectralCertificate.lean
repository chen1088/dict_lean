import DictatorshipTesting.Paper.Aux_SpectralCertificateBridge

/-!
# Lemma 5.2: Spectral certificate

This is `lem:spectral-certificate` from `soda27authors_section5_rethought.tex`.
-/

namespace DictatorshipTesting

/-- Lemma 5.2, `lem:spectral-certificate`: spectral certificate. -/
theorem L5_2_SpectralCertificate (m : ℕ) (c : ℝ) :
    (0 ≤ c →
      (∀ lam : YoungDiagram (2 * m),
        ¬ IsOneRow lam → ¬ IsStandard lam → c * youngDim lam ≤ hEven m lam) →
      MatchingSpectralGapConstant (2 * m) c) ∧
    (0 ≤ c →
      (∀ lam : YoungDiagram (2 * m + 1),
        ¬ IsOneRow lam → ¬ IsStandard lam → c * youngDim lam ≤ hOdd m lam) →
      MatchingSpectralGapConstant (2 * m + 1) c) := by
  constructor
  · intro hc hcert
    exact matchingSpectralGap_of_even_young_certificate m c hc hcert
  · intro hc hcert
    exact matchingSpectralGap_of_odd_young_certificate m c hc hcert

end DictatorshipTesting
