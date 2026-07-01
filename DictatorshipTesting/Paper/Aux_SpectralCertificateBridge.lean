import DictatorshipTesting.Paper.Defs

/-!
# Spectral-certificate bridge

This is the representation-theoretic input behind Lemma 5.2.  Once the regular
representation of `S_n` is decomposed into Young-diagram blocks, the scalar of
the averaged matching-high-degree operator on a block is the corresponding
high-character count divided by the Specht dimension.

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
  -- TODO: decompose `L^2(S_{2m})` into Young blocks, show that the averaged
  -- high-character operator is central, and identify its block scalar with
  -- `hEven m lam / youngDim lam`.
  sorry

/-- Odd spectral bridge: finite Young-diagram inequalities imply the matching
spectral gap for `S_{2m+1}`. -/
theorem matchingSpectralGap_of_odd_young_certificate (m : ℕ) (c : ℝ)
    (hc : 0 ≤ c)
    (hcert :
      ∀ lam : YoungDiagram (2 * m + 1),
        ¬ IsOneRow lam → ¬ IsStandard lam → c * youngDim lam ≤ hOdd m lam) :
    MatchingSpectralGapConstant (2 * m + 1) c := by
  -- TODO: repeat the even bridge after the one-box branching step for the
  -- unmatched point in a near-perfect matching.
  sorry

end DictatorshipTesting
