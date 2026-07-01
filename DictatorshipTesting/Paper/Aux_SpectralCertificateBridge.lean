import DictatorshipTesting.Paper.Aux_SpectralBridgeFromRepresentationInput

/-!
# Spectral-certificate bridge

This is the public bridge used by Lemma 5.2.  The representation-theoretic
boundary is split into:

* `Aux_MatchingSubgroupRestrictionInput`
* `Aux_LocalTruncationTraceInput`
* `Aux_CentralizationOverMatchings`
* `Aux_SpectralBridgeFromRepresentationInput`

This is intentionally the only Section 5 file that should need the full
representation theory of the symmetric group.  The certificate inequalities
themselves live in finite combinatorial aux files.
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
  have hrestrict : MatchingSubgroupRestrictionEvenInput m :=
    matchingSubgroupRestriction_even_specht_pieri_input m
  have htrace : LocalTruncationTraceEvenInput m :=
    localTruncationTrace_even_from_restriction m hrestrict
  exact
    matchingSpectralGap_of_even_young_certificate_input
      m c hc hrestrict htrace hcert

/-- Odd spectral bridge: finite Young-diagram inequalities imply the matching
spectral gap for `S_{2m+1}`. -/
theorem matchingSpectralGap_of_odd_young_certificate (m : ℕ) (c : ℝ)
    (hc : 0 ≤ c)
    (hcert :
      ∀ lam : YoungDiagram (2 * m + 1),
        ¬ IsOneRow lam → ¬ IsStandard lam → c * youngDim lam ≤ hOdd m lam) :
    MatchingSpectralGapConstant (2 * m + 1) c := by
  have hrestrict : MatchingSubgroupRestrictionOddInput m :=
    matchingSubgroupRestriction_odd_specht_pieri_input m
  have htrace : LocalTruncationTraceOddInput m :=
    localTruncationTrace_odd_from_restriction m hrestrict
  exact
    matchingSpectralGap_of_odd_young_certificate_input
      m c hc hrestrict htrace hcert

end DictatorshipTesting
