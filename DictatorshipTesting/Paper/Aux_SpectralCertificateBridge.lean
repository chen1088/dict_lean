import DictatorshipTesting.Paper.Aux_SpectralGapFromCertificates

/-!
# Spectral-certificate bridge

This is the public bridge used by Lemma 5.2.  The representation-theoretic
boundary is split into:

* `Aux_MatchingRestrictionInput`
* `Aux_LocalCharacterProjection`
* `Aux_TraceLocalTruncation`
* `Aux_CentralizationBridge`
* `Aux_SpectralGapFromCertificates`

The certificate inequalities themselves live in finite combinatorial aux files.
-/

noncomputable section

namespace DictatorshipTesting

/-- Even spectral bridge: finite Young-diagram inequalities imply the matching
spectral gap for `S_{2m}`. -/
theorem matchingSpectralGap_of_even_young_certificate (m : ℕ) (c : ℝ)
    (hc : 0 ≤ c)
    (hcert :
      ∀ lam : YoungDiagram (2 * m),
        ¬ IsOneRow lam → ¬ IsStandard lam → c * youngDim lam ≤ hEven m lam) :
    MatchingSpectralGapConstant (2 * m) c := by
  have hrestrict : MatchingRestrictionEvenInput m :=
    matchingRestriction_even_specht_pieri_input m
  have htrace : TraceLocalTruncationEvenInput m :=
    traceLocalTruncation_even_from_restriction m hrestrict
  exact
    spectralGapFromEvenCertificates_input
      m c hc hrestrict htrace hcert

/-- Odd spectral bridge: finite Young-diagram inequalities imply the matching
spectral gap for `S_{2m+1}`. -/
theorem matchingSpectralGap_of_odd_young_certificate (m : ℕ) (c : ℝ)
    (hc : 0 ≤ c)
    (hcert :
      ∀ lam : YoungDiagram (2 * m + 1),
        ¬ IsOneRow lam → ¬ IsStandard lam → c * youngDim lam ≤ hOdd m lam) :
    MatchingSpectralGapConstant (2 * m + 1) c := by
  have hrestrict : MatchingRestrictionOddInput m :=
    matchingRestriction_odd_specht_pieri_input m
  have htrace : TraceLocalTruncationOddInput m :=
    traceLocalTruncation_odd_from_restriction m hrestrict
  exact
    spectralGapFromOddCertificates_input
      m c hc hrestrict htrace hcert

end DictatorshipTesting
