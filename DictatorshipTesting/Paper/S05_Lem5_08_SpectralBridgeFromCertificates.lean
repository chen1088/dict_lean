import DictatorshipTesting.Paper.Aux_SpectralBridgeRepresentationInputs
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

/-- The trace/scalar formula plus a finite certificate inequality gives a lower
bound on the scalar of each non-`U_1` block. -/
theorem blockScalar_lower_bound_of_traceScalarFormula {n : ℕ}
    {height theta : YoungDiagram n → ℝ} {c : ℝ}
    (htraceScalar : TraceScalarValueInput height theta)
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

/-- Dimension positivity plus the block trace identity imply the trace/scalar
value formula.  This is the algebraic part of Lemma 5.8(D). -/
theorem traceScalarValue_of_blockTraceIdentity {n : ℕ}
    {height theta : YoungDiagram n → ℝ}
    (hdim : YoungDimensionPositiveInput n)
    (htrace : BlockTraceIdentityInput height theta) :
    TraceScalarValueInput height theta := by
  intro lam
  have hpos : 0 < youngDim lam := hdim lam
  exact ⟨hpos,
    centralizationBridge_scalar_eq_trace_div_dimension
      (youngDim lam) (height lam) (theta lam) (ne_of_gt hpos) (htrace lam)⟩

/-- Convert a scalarity-plus-trace package into the scalar-value package used
by the spectral-gap wrapper. -/
def matchingAverageScalarModel_of_blockTraceModel {n : ℕ}
    {height : YoungDiagram n → ℝ} {F : Perm (Fin n) → ℝ}
    {blockEnergy : YoungDiagram n → ℝ}
    (hdim : YoungDimensionPositiveInput n)
    (model : MatchingAverageBlockTraceModel height F blockEnergy) :
    MatchingAverageScalarModel height F blockEnergy where
  theta := model.theta
  scalarity := model.scalarity
  trace_value :=
    traceScalarValue_of_blockTraceIdentity hdim model.trace_identity

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

/-- Spectral gap from scalar lower bounds on every non-`U_1` Young block.

This is the purely algebraic wrapper in Lemma 5.8: once the block energies,
`U_1` identification, matching-average scalarity, and scalar lower bounds are
available, no representation theory remains. -/
theorem SpectralGapFromBlockScalarLowerBounds {n : ℕ} (c : ℝ)
    (F : Perm (Fin n) → ℝ)
    (blockEnergy theta : YoungDiagram n → ℝ)
    (hdecomp : YoungBlockDecompositionInput blockEnergy)
    (hu1 : U1YoungBlockIdentificationInput F blockEnergy)
    (hscalarity : MatchingAverageScalarityInput F blockEnergy theta)
    (hscalar_lb : ∀ lam ∈ nonU1YoungBlocks n, c ≤ theta lam) :
    c * l2DistSqToU1 F ≤ matchingMeanProjectionError F := by
  exact SpectralGapFromBlockScalars c F blockEnergy theta hdecomp hu1 hscalarity
    hscalar_lb

/-- Even spectral model hypotheses for all sizes used downstream. -/
def EvenSpectralBlockModelFamily : Prop :=
  ∀ m : ℕ, 2 ≤ m →
    SpectralBlockModelInput (fun lam : YoungDiagram (2 * m) => hEven m lam)

/-- Odd spectral model hypotheses for all sizes used downstream. -/
def OddSpectralBlockModelFamily : Prop :=
  ∀ m : ℕ, 2 ≤ m →
    SpectralBlockModelInput (fun lam : YoungDiagram (2 * m + 1) => hOdd m lam)

/-- External even spectral-block model from standard representation theory.

References:
* regular representation decomposition and Specht classification, e.g. Sagan,
  *The Symmetric Group*;
* Littlewood--Richardson restriction of Specht modules to Young subgroups,
  James--Kerber, *The Representation Theory of the Symmetric Group*, Section
  2.8.13; Bowman--De Visscher--Orellana, arXiv:1210.5579, Theorem 1.1 quotes
  this statement and notes that transitivity determines restriction to any
  Young subgroup;
* the two-strip Pieri specializations for the matching subgroup chain
  `S_{2m} ⊃ S_{2m-2} × S_2 ⊃ ... ⊃ S_2^m`;
* Schur's lemma for scalarity of the matching-averaged operator on each
  regular Young block.

This is the exact representation-theoretic bridge not formalized in Mathlib:
it supplies the genuine Young-block energies, identifies the `U_1` blocks, and
identifies the matching-average scalar as `hEven m lam / youngDim lam`. -/
axiom spectralBlockModelInput_even_from_specht_pieri_schur
    (m : ℕ) (hm : 2 ≤ m) :
    SpectralBlockModelInput (fun lam : YoungDiagram (2 * m) => hEven m lam)

/-- External odd spectral-block model from the same representation-theoretic
inputs as the even case, with one initial ordinary Specht branching step from
`S_{2m+1}` to `S_{2m} × S_1`. -/
axiom spectralBlockModelInput_odd_from_specht_pieri_schur
    (m : ℕ) (hm : 2 ≤ m) :
    SpectralBlockModelInput (fun lam : YoungDiagram (2 * m + 1) => hOdd m lam)

/-- Bundled even spectral-block model family supplied by the external
Specht/Pieri/Schur input. -/
theorem evenSpectralBlockModelFamily_from_specht_pieri_schur :
    EvenSpectralBlockModelFamily := by
  intro m hm
  exact spectralBlockModelInput_even_from_specht_pieri_schur m hm

/-- Bundled odd spectral-block model family supplied by the external
Specht/Pieri/Schur input. -/
theorem oddSpectralBlockModelFamily_from_specht_pieri_schur :
    OddSpectralBlockModelFamily := by
  intro m hm
  exact spectralBlockModelInput_odd_from_specht_pieri_schur m hm

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
  rcases hmodel F with ⟨energy, ⟨scalar⟩⟩
  exact
    SpectralGapFromBlockScalars c F energy.blockEnergy scalar.theta
      energy.nonneg energy.u1_identification scalar.scalarity
      (blockScalar_lower_bound_of_traceScalarFormula scalar.trace_value hcert)

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
  rcases hmodel F with ⟨energy, ⟨scalar⟩⟩
  exact
    SpectralGapFromBlockScalars c F energy.blockEnergy scalar.theta
      energy.nonneg energy.u1_identification scalar.scalarity
      (blockScalar_lower_bound_of_traceScalarFormula scalar.trace_value hcert)

/-- Even spectral bridge: finite Young-diagram inequalities imply the matching
spectral gap for `S_{2m}`. -/
theorem matchingSpectralGap_of_even_young_certificate (m : ℕ) (hm : 2 ≤ m) (c : ℝ)
    (hmodel : SpectralBlockModelInput
      (fun lam : YoungDiagram (2 * m) => hEven m lam))
    (_hc : 0 ≤ c)
    (hcert :
      ∀ lam : YoungDiagram (2 * m),
        ¬ IsOneRow lam → ¬ IsStandard lam → c * youngDim lam ≤ hEven m lam) :
    MatchingSpectralGapConstant (2 * m) c := by
  exact EvenSpectralGapFromCertificates m hm c hmodel hcert

/-- Odd spectral bridge: finite Young-diagram inequalities imply the matching
spectral gap for `S_{2m+1}`. -/
theorem matchingSpectralGap_of_odd_young_certificate (m : ℕ) (hm : 2 ≤ m) (c : ℝ)
    (hmodel : SpectralBlockModelInput
      (fun lam : YoungDiagram (2 * m + 1) => hOdd m lam))
    (_hc : 0 ≤ c)
    (hcert :
      ∀ lam : YoungDiagram (2 * m + 1),
        ¬ IsOneRow lam → ¬ IsStandard lam → c * youngDim lam ≤ hOdd m lam) :
    MatchingSpectralGapConstant (2 * m + 1) c := by
  exact OddSpectralGapFromCertificates m hm c hmodel hcert

/-- Lemma 5.8, `lem:spectral-certificate`: spectral certificate, conditional
on the representation-theoretic spectral block models.  This preserves the old
theorem name `L5_2_SpectralCertificate`. -/
theorem L5_2_SpectralCertificate (m : ℕ) (hm : 2 ≤ m) (c : ℝ)
    (hevenModel : SpectralBlockModelInput
      (fun lam : YoungDiagram (2 * m) => hEven m lam))
    (hoddModel : SpectralBlockModelInput
      (fun lam : YoungDiagram (2 * m + 1) => hOdd m lam)) :
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
    exact matchingSpectralGap_of_even_young_certificate m hm c hevenModel hc hcert
  · intro hc hcert
    exact matchingSpectralGap_of_odd_young_certificate m hm c hoddModel hc hcert

end DictatorshipTesting
