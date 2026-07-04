import DictatorshipTesting.Paper.Aux_SpectralBridgeFromCertificates_Legacy

/-!
Paper statement: Lemma 5.28 (`lem:block-lower-bound-gap`)
Title in paper: Block lower bound implies the gap.

Status: paper-facing wrapper around the existing algebraic spectral-gap
comparison.
-/

noncomputable section

namespace DictatorshipTesting

open scoped BigOperators

/-- Lemma 5.28: scalar lower bounds on all non-`U_1` blocks imply the matching
spectral gap. -/
theorem S05_Lem5_28_block_lower_bound_implies_gap {n : Nat} (c : ℝ)
    (F : Perm (Fin n) -> ℝ)
    (blockEnergy theta : YoungDiagram n -> ℝ)
    (hdecomp : YoungBlockDecompositionInput blockEnergy)
    (hu1 : U1YoungBlockIdentificationInput F blockEnergy)
    (hscalarity : MatchingAverageScalarityInput F blockEnergy theta)
    (hscalar_lb : ∀ lam ∈ nonU1YoungBlocks n, c ≤ theta lam) :
    c * l2DistSqToU1 F ≤ matchingMeanProjectionError F := by
  exact SpectralGapFromBlockScalarLowerBounds c F blockEnergy theta
    hdecomp hu1 hscalarity hscalar_lb

/-- Lemma 5.28 paper-numbered alias for the direct weighted-sum comparison. -/
theorem S05_Lem5_28_spectralGapFromBlockScalars {n : Nat} (c : ℝ)
    (F : Perm (Fin n) -> ℝ)
    (blockEnergy theta : YoungDiagram n -> ℝ)
    (hdecomp : YoungBlockDecompositionInput blockEnergy)
    (hu1 : U1YoungBlockIdentificationInput F blockEnergy)
    (hscalarity : MatchingAverageScalarityInput F blockEnergy theta)
    (hscalar_lb : ∀ lam ∈ nonU1YoungBlocks n, c ≤ theta lam) :
    c * l2DistSqToU1 F ≤ matchingMeanProjectionError F := by
  exact SpectralGapFromBlockScalars c F blockEnergy theta hdecomp hu1 hscalarity
    hscalar_lb

/-- Lemma 5.28 paper-numbered alias: the trace/scalar formula plus the finite
certificate gives scalar lower bounds on non-`U_1` blocks. -/
theorem S05_Lem5_28_blockScalar_lower_bound_of_traceScalarFormula {n : Nat}
    {height theta : YoungDiagram n -> ℝ} {c : ℝ}
    (htraceScalar : TraceScalarValueInput height theta)
    (hcert :
      ∀ lam : YoungDiagram n,
        ¬ IsOneRow lam -> ¬ IsStandard lam -> c * youngDim lam ≤ height lam) :
    ∀ lam ∈ nonU1YoungBlocks n, c ≤ theta lam := by
  exact blockScalar_lower_bound_of_traceScalarFormula htraceScalar hcert

/-- Lemma 5.28 paper-numbered alias: dimension positivity and block trace
identity imply the scalar value formula. -/
theorem S05_Lem5_28_traceScalarValue_of_blockTraceIdentity {n : Nat}
    {height theta : YoungDiagram n -> ℝ}
    (hdim : YoungDimensionPositiveInput n)
    (htrace : BlockTraceIdentityInput height theta) :
    TraceScalarValueInput height theta := by
  exact traceScalarValue_of_blockTraceIdentity hdim htrace

end DictatorshipTesting
