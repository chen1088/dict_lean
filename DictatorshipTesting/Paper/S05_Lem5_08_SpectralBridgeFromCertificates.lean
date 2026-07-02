import DictatorshipTesting.Paper.S05_Lem5_06_CentralizationOverMatchings

/-!
Paper statement: Lemma 5.8 (`lem:spectral-certificate`)
Title in paper: Spectral bridge from the finite certificate.

Status: representation-theoretic bridge input after the local trace and
centralization components have been isolated.
-/

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
    (m : ℕ) (hm : 2 ≤ m) (c : ℝ)
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
    (m : ℕ) (hm : 2 ≤ m) (c : ℝ)
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

/-- Even spectral bridge: finite Young-diagram inequalities imply the matching
spectral gap for `S_{2m}`. -/
theorem matchingSpectralGap_of_even_young_certificate (m : ℕ) (hm : 2 ≤ m) (c : ℝ)
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
      m hm c hc hrestrict htrace hcert

/-- Odd spectral bridge: finite Young-diagram inequalities imply the matching
spectral gap for `S_{2m+1}`. -/
theorem matchingSpectralGap_of_odd_young_certificate (m : ℕ) (hm : 2 ≤ m) (c : ℝ)
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
      m hm c hc hrestrict htrace hcert

/-- Lemma 5.8, `lem:spectral-certificate`: spectral certificate.  This
preserves the old theorem name `L5_2_SpectralCertificate`. -/
theorem L5_2_SpectralCertificate (m : ℕ) (hm : 2 ≤ m) (c : ℝ) :
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
    exact matchingSpectralGap_of_even_young_certificate m hm c hc hcert
  · intro hc hcert
    exact matchingSpectralGap_of_odd_young_certificate m hm c hc hcert

end DictatorshipTesting
