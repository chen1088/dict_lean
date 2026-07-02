import DictatorshipTesting.Paper.S05_Lem5_06_CentralizationOverMatchings

/-!
Paper statement: Lemma 5.8 (`lem:spectral-certificate`)
Title in paper: Spectral bridge from the finite certificate.

Status: the algebraic block-scalar implication is proved below.  The remaining
inputs are exactly the representation-theoretic construction of Young-block
energies and scalars from the regular representation, the identification of the
`U_1` summand, and Schur-lemma scalarity of the averaged matching operator.
-/

/-!
# Spectral gap from certificate inequalities

This file separates the final Section 5 bridge into two layers.

The proved layer is finite algebra: if the `U_1`-orthogonal energy of `F`
decomposes as a finite sum of nonnegative Young-block energies, and the matching
projection error is the same sum weighted by block scalars bounded below by
`c`, then the matching spectral gap with constant `c` follows.

The unproved layer is representation theory: constructing those block energies
and scalars from the Young-block decomposition of `L^2(S_n)`, identifying the
two `U_1` blocks `(n)` and `(n-1,1)`, and proving scalarity of the averaged
matching operator by Schur's lemma.
-/

noncomputable section

namespace DictatorshipTesting

open scoped BigOperators

/-- Young blocks outside the two blocks that form `U_1`: `(n)` and `(n-1,1)`.
The predicates are stated in the concrete row-language used by this scaffold. -/
def nonU1YoungBlocks (n : ℕ) : Finset (YoungDiagram n) := by
  classical
  exact Finset.univ.filter (fun lam : YoungDiagram n =>
    ¬ IsOneRow lam ∧ ¬ IsStandard lam)

/-- The Young-block decomposition supplies nonnegative squared energies for
each Young block.  This is the abstract numerical shadow of orthogonality of the
regular Young decomposition. -/
def YoungBlockDecompositionInput {n : ℕ}
    (blockEnergy : YoungDiagram n → ℝ) : Prop :=
  ∀ lam : YoungDiagram n, 0 ≤ blockEnergy lam

/-- The degree-one space `U_1` is exactly the sum of the one-row and standard
Young blocks, so the distance to `U_1` is the sum of the remaining block
energies. -/
def U1YoungBlockIdentificationInput {n : ℕ}
    (F : Perm (Fin n) → ℝ) (blockEnergy : YoungDiagram n → ℝ) : Prop :=
  l2DistSqToU1 F = (nonU1YoungBlocks n).sum blockEnergy

/-- Scalarity of the matching average on Young blocks: the matching projection
error is the block-energy sum weighted by the scalar on each block. -/
def MatchingAverageScalarityInput {n : ℕ}
    (F : Perm (Fin n) → ℝ)
    (blockEnergy theta : YoungDiagram n → ℝ) : Prop :=
  matchingMeanProjectionError F =
    (nonU1YoungBlocks n).sum (fun lam => theta lam * blockEnergy lam)

/-- Trace/scalar formula supplied by the local trace calculation and the
trace-divided-by-block-dimension algebra: `theta_lambda = h(lambda)/d_lambda`.
The positivity of `d_lambda` is included because division by the Young-block
dimension is part of the scalar formula. -/
def TraceScalarFormula {n : ℕ}
    (height theta : YoungDiagram n → ℝ) : Prop :=
  ∀ lam : YoungDiagram n,
    0 < youngDim lam ∧ theta lam = height lam / youngDim lam

/-- A compact package of the representation-theoretic block model used by the
algebraic spectral-gap wrapper. -/
def SpectralBlockModelInput {n : ℕ}
    (height : YoungDiagram n → ℝ) : Prop :=
  ∀ F : Perm (Fin n) → ℝ,
    ∃ blockEnergy theta : YoungDiagram n → ℝ,
      YoungBlockDecompositionInput blockEnergy ∧
      U1YoungBlockIdentificationInput F blockEnergy ∧
      MatchingAverageScalarityInput F blockEnergy theta ∧
      TraceScalarFormula height theta

/-- The trace/scalar formula plus a finite certificate inequality gives a lower
bound on the scalar of each non-`U_1` block. -/
theorem blockScalar_lower_bound_of_traceScalarFormula {n : ℕ}
    {height theta : YoungDiagram n → ℝ} {c : ℝ}
    (htraceScalar : TraceScalarFormula height theta)
    (hcert :
      ∀ lam : YoungDiagram n,
        ¬ IsOneRow lam → ¬ IsStandard lam → c * youngDim lam ≤ height lam) :
    ∀ lam ∈ nonU1YoungBlocks n, c ≤ theta lam := by
  classical
  intro lam hlam
  have hnot_row : ¬ IsOneRow lam := (Finset.mem_filter.mp hlam).2.1
  have hnot_std : ¬ IsStandard lam := (Finset.mem_filter.mp hlam).2.2
  rcases htraceScalar lam with ⟨hdim_pos, htheta⟩
  rw [htheta]
  exact (le_div_iff₀ hdim_pos).mpr (hcert lam hnot_row hnot_std)

/-- Abstract finite-dimensional spectral wrapper.  Once the Young-block energy
and scalar identities are available, the spectral gap is just a weighted-sum
comparison. -/
theorem SpectralGapFromBlockScalars {n : ℕ} (c : ℝ)
    (F : Perm (Fin n) → ℝ)
    (blockEnergy theta : YoungDiagram n → ℝ)
    (hdecomp : YoungBlockDecompositionInput blockEnergy)
    (hu1 : U1YoungBlockIdentificationInput F blockEnergy)
    (hscalarity : MatchingAverageScalarityInput F blockEnergy theta)
    (hscalar_lb : ∀ lam ∈ nonU1YoungBlocks n, c ≤ theta lam) :
    c * l2DistSqToU1 F ≤ matchingMeanProjectionError F := by
  classical
  rw [hu1, hscalarity]
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun lam hlam => by
    exact mul_le_mul_of_nonneg_right (hscalar_lb lam hlam) (hdecomp lam))

/-- Even representation-theoretic block model.  This is the precise remaining
input behind the even bridge: regular Young-block decomposition, `U_1`
identification, matching-average scalarity, and the trace/scalar formula. -/
theorem evenSpectralBlockModel_from_representation_input
    (m : ℕ) (hm : 2 ≤ m)
    (_hrestrict : MatchingRestrictionEvenInput m)
    (_htrace : TraceLocalTruncationEvenInput m) :
    SpectralBlockModelInput (fun lam : YoungDiagram (2 * m) => hEven m lam) := by
  -- Formalizing this requires Specht modules, the regular representation
  -- decomposition, the `U_1` Young-block identification, and Schur-lemma
  -- scalarity of the averaged matching operator.
  sorry

/-- Odd representation-theoretic block model.  This is the analogous input for
`S_{2m+1}`. -/
theorem oddSpectralBlockModel_from_representation_input
    (m : ℕ) (hm : 2 ≤ m)
    (_hrestrict : MatchingRestrictionOddInput m)
    (_htrace : TraceLocalTruncationOddInput m) :
    SpectralBlockModelInput (fun lam : YoungDiagram (2 * m + 1) => hOdd m lam) := by
  -- Formalizing this requires the odd Young-block decomposition, ordinary
  -- one-box branching for the unmatched point, and the same Schur-lemma
  -- scalarity argument.
  sorry

/-- Even spectral bridge: the representation-theoretic block model plus finite
Young-diagram certificates imply the matching spectral gap on `S_{2m}`. -/
theorem EvenSpectralGapFromCertificates (m : ℕ) (_hm : 2 ≤ m) (c : ℝ)
    (hmodel : SpectralBlockModelInput
      (fun lam : YoungDiagram (2 * m) => hEven m lam))
    (hcert :
      ∀ lam : YoungDiagram (2 * m),
        ¬ IsOneRow lam → ¬ IsStandard lam → c * youngDim lam ≤ hEven m lam) :
    MatchingSpectralGapConstant (2 * m) c := by
  intro F
  rcases hmodel F with
    ⟨blockEnergy, theta, hdecomp, hu1, hscalarity, htraceScalar⟩
  exact
    SpectralGapFromBlockScalars c F blockEnergy theta hdecomp hu1 hscalarity
      (blockScalar_lower_bound_of_traceScalarFormula htraceScalar hcert)

/-- Odd spectral bridge: the representation-theoretic block model plus finite
Young-diagram certificates imply the matching spectral gap on `S_{2m+1}`. -/
theorem OddSpectralGapFromCertificates (m : ℕ) (_hm : 2 ≤ m) (c : ℝ)
    (hmodel : SpectralBlockModelInput
      (fun lam : YoungDiagram (2 * m + 1) => hOdd m lam))
    (hcert :
      ∀ lam : YoungDiagram (2 * m + 1),
        ¬ IsOneRow lam → ¬ IsStandard lam → c * youngDim lam ≤ hOdd m lam) :
    MatchingSpectralGapConstant (2 * m + 1) c := by
  intro F
  rcases hmodel F with
    ⟨blockEnergy, theta, hdecomp, hu1, hscalarity, htraceScalar⟩
  exact
    SpectralGapFromBlockScalars c F blockEnergy theta hdecomp hu1 hscalarity
      (blockScalar_lower_bound_of_traceScalarFormula htraceScalar hcert)

/-- Even spectral bridge: finite Young-diagram inequalities imply the matching
spectral gap for `S_{2m}`. -/
theorem matchingSpectralGap_of_even_young_certificate (m : ℕ) (hm : 2 ≤ m) (c : ℝ)
    (_hc : 0 ≤ c)
    (hcert :
      ∀ lam : YoungDiagram (2 * m),
        ¬ IsOneRow lam → ¬ IsStandard lam → c * youngDim lam ≤ hEven m lam) :
    MatchingSpectralGapConstant (2 * m) c := by
  have hrestrict : MatchingRestrictionEvenInput m :=
    matchingRestriction_even_specht_pieri_input m
  have htrace : TraceLocalTruncationEvenInput m :=
    traceLocalTruncation_even_from_restriction m hrestrict
  have hmodel : SpectralBlockModelInput
      (fun lam : YoungDiagram (2 * m) => hEven m lam) :=
    evenSpectralBlockModel_from_representation_input m hm hrestrict htrace
  exact EvenSpectralGapFromCertificates m hm c hmodel hcert

/-- Odd spectral bridge: finite Young-diagram inequalities imply the matching
spectral gap for `S_{2m+1}`. -/
theorem matchingSpectralGap_of_odd_young_certificate (m : ℕ) (hm : 2 ≤ m) (c : ℝ)
    (_hc : 0 ≤ c)
    (hcert :
      ∀ lam : YoungDiagram (2 * m + 1),
        ¬ IsOneRow lam → ¬ IsStandard lam → c * youngDim lam ≤ hOdd m lam) :
    MatchingSpectralGapConstant (2 * m + 1) c := by
  have hrestrict : MatchingRestrictionOddInput m :=
    matchingRestriction_odd_specht_pieri_input m
  have htrace : TraceLocalTruncationOddInput m :=
    traceLocalTruncation_odd_from_restriction m hrestrict
  have hmodel : SpectralBlockModelInput
      (fun lam : YoungDiagram (2 * m + 1) => hOdd m lam) :=
    oddSpectralBlockModel_from_representation_input m hm hrestrict htrace
  exact OddSpectralGapFromCertificates m hm c hmodel hcert

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
