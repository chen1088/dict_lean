import DictatorshipTesting.Paper.Aux_SpectralBridgeFromCertificates
import DictatorshipTesting.Paper.Aux_SpectralBridgeDimensionParam

/-
Direct reverse imports (generated):
- `DictatorshipTesting.PaperAux`
- `DictatorshipTesting.PaperPlaceholders`
-/

/-!
Paper statement: Lemma 5.31 (`lem:block-lower-bound-gap`)
Title in paper: Block lower bound implies the gap.

Status: proven. Paper-facing wrapper around the existing algebraic spectral-gap
comparison.
-/

noncomputable section

namespace DictatorshipTesting

open scoped BigOperators

/-- Lemma 5.31: scalar lower bounds on all non-`U_1` blocks imply the matching
spectral gap. -/
theorem S05_Lem5_31_block_lower_bound_implies_gap {n : Nat} (c : ℝ)
    (F : Perm (Fin n) -> ℝ)
    (blockEnergy theta : YoungDiagram n -> ℝ)
    (hdecomp : YoungBlockDecompositionInput blockEnergy)
    (hu1 : U1YoungBlockIdentificationInput F blockEnergy)
    (hscalarity : MatchingAverageScalarityInput F blockEnergy theta)
    (hscalar_lb : ∀ lam ∈ nonU1YoungBlocks n, c ≤ theta lam) :
    c * l2DistSqToU1 F ≤ matchingMeanProjectionError F := by
  exact SpectralGapFromBlockScalarLowerBounds c F blockEnergy theta
    hdecomp hu1 hscalarity hscalar_lb

/-- Lemma 5.31 paper-numbered alias for the direct weighted-sum comparison. -/
theorem S05_Lem5_31_spectralGapFromBlockScalars {n : Nat} (c : ℝ)
    (F : Perm (Fin n) -> ℝ)
    (blockEnergy theta : YoungDiagram n -> ℝ)
    (hdecomp : YoungBlockDecompositionInput blockEnergy)
    (hu1 : U1YoungBlockIdentificationInput F blockEnergy)
    (hscalarity : MatchingAverageScalarityInput F blockEnergy theta)
    (hscalar_lb : ∀ lam ∈ nonU1YoungBlocks n, c ≤ theta lam) :
    c * l2DistSqToU1 F ≤ matchingMeanProjectionError F := by
  exact SpectralGapFromBlockScalars c F blockEnergy theta hdecomp hu1 hscalarity
    hscalar_lb

/-- Lemma 5.31 paper-numbered alias: the trace/scalar formula plus the finite
certificate gives scalar lower bounds on non-`U_1` blocks. -/
theorem S05_Lem5_31_blockScalar_lower_bound_of_traceScalarFormula {n : Nat}
    {height theta : YoungDiagram n -> ℝ} {c : ℝ}
    (htraceScalar : TraceScalarValueInput height theta)
    (hcert :
      ∀ lam : YoungDiagram n,
        ¬ IsOneRow lam -> ¬ IsStandard lam -> c * youngDim lam ≤ height lam) :
    ∀ lam ∈ nonU1YoungBlocks n, c ≤ theta lam := by
  exact blockScalar_lower_bound_of_traceScalarFormula htraceScalar hcert

/-- Lemma 5.31 paper-numbered alias: dimension positivity and block trace
identity imply the scalar value formula. -/
theorem S05_Lem5_31_traceScalarValue_of_blockTraceIdentity {n : Nat}
    {height theta : YoungDiagram n -> ℝ}
    (hdim : YoungDimensionPositiveInput n)
    (htrace : BlockTraceIdentityInput height theta) :
    TraceScalarValueInput height theta := by
  exact traceScalarValue_of_blockTraceIdentity hdim htrace

/-- Lemma 5.31 paper-numbered alias: spectral gap from scalarity, block trace
identity, dimension positivity, and a finite certificate. -/
theorem S05_Lem5_31_spectralGapFromBlockTraceModel {n : Nat} (c : ℝ)
    (F : Perm (Fin n) -> ℝ)
    (height blockEnergy : YoungDiagram n -> ℝ)
    (hdecomp : YoungBlockDecompositionInput blockEnergy)
    (hu1 : U1YoungBlockIdentificationInput F blockEnergy)
    (hdim : YoungDimensionPositiveInput n)
    (htraceModel : MatchingAverageBlockTraceModel height F blockEnergy)
    (hcert :
      ∀ lam : YoungDiagram n,
        ¬ IsOneRow lam -> ¬ IsStandard lam -> c * youngDim lam <= height lam) :
    c * l2DistSqToU1 F <= matchingMeanProjectionError F := by
  let scalar :=
    matchingAverageScalarModel_of_blockTraceModel hdim htraceModel
  exact
    SpectralGapFromBlockScalars c F blockEnergy scalar.theta
      hdecomp hu1 scalar.scalarity
      (blockScalar_lower_bound_of_traceScalarFormula scalar.trace_value hcert)

/-- Lemma 5.31 dimension-parameterized alias: trace/scalar formula plus a
finite certificate gives scalar lower bounds on non-`U_1` blocks. -/
theorem S05_Lem5_31_blockScalar_lower_bound_withDim {n : Nat}
    {dim height theta : YoungDiagram n -> ℝ} {c : ℝ}
    (htraceScalar : TraceScalarValueInputWithDim dim height theta)
    (hcert :
      ∀ lam : YoungDiagram n,
        ¬ IsOneRow lam -> ¬ IsStandard lam -> c * dim lam <= height lam) :
    ∀ lam ∈ nonU1YoungBlocks n, c <= theta lam := by
  exact blockScalar_lower_bound_of_traceScalarFormula_withDim htraceScalar hcert

/-- Lemma 5.31 dimension-parameterized alias: positive dimension plus the block
trace identity imply the scalar value formula. -/
theorem S05_Lem5_31_traceScalarValue_of_blockTraceIdentity_withDim {n : Nat}
    {dim height theta : YoungDiagram n -> ℝ}
    (hdim : YoungDimensionPositiveInputWithDim dim)
    (htrace : BlockTraceIdentityInputWithDim dim height theta) :
    TraceScalarValueInputWithDim dim height theta := by
  exact traceScalarValue_of_blockTraceIdentity_withDim hdim htrace

/-- Lemma 5.31 dimension-parameterized alias: spectral gap from scalarity,
trace/scalar formula, and a certificate with respect to an arbitrary dimension
function. -/
theorem S05_Lem5_31_spectralGapFromBlockScalarsWithDim {n : Nat} (c : ℝ)
    (F : Perm (Fin n) -> ℝ)
    (dim height blockEnergy theta : YoungDiagram n -> ℝ)
    (hdecomp : YoungBlockDecompositionInput blockEnergy)
    (hu1 : U1YoungBlockIdentificationInput F blockEnergy)
    (hscalarity : MatchingAverageScalarityInput F blockEnergy theta)
    (htrace : TraceScalarValueInputWithDim dim height theta)
    (hcert :
      ∀ lam : YoungDiagram n,
        ¬ IsOneRow lam -> ¬ IsStandard lam -> c * dim lam <= height lam) :
    c * l2DistSqToU1 F <= matchingMeanProjectionError F := by
  exact SpectralGapFromBlockScalarsWithDim c F dim height blockEnergy theta
    hdecomp hu1 hscalarity htrace hcert

/-- Lemma 5.31 dimension-parameterized alias: spectral gap from scalarity,
block trace identity, dimension positivity, and a certificate with respect to
an arbitrary dimension function. -/
theorem S05_Lem5_31_spectralGapFromBlockTraceModelWithDim {n : Nat} (c : ℝ)
    (F : Perm (Fin n) -> ℝ)
    (dim height blockEnergy : YoungDiagram n -> ℝ)
    (hdecomp : YoungBlockDecompositionInput blockEnergy)
    (hu1 : U1YoungBlockIdentificationInput F blockEnergy)
    (hdim : YoungDimensionPositiveInputWithDim dim)
    (htraceModel : MatchingAverageBlockTraceModelWithDim dim height F blockEnergy)
    (hcert :
      ∀ lam : YoungDiagram n,
        ¬ IsOneRow lam -> ¬ IsStandard lam -> c * dim lam <= height lam) :
    c * l2DistSqToU1 F <= matchingMeanProjectionError F := by
  let scalar :=
    matchingAverageScalarModel_of_blockTraceModel_withDim hdim htraceModel
  exact
    SpectralGapFromBlockScalarsWithDim c F dim height blockEnergy scalar.theta
      hdecomp hu1 scalar.scalarity scalar.trace_value hcert

/-- Lemma 5.31 dimension-parameterized alias: a parameterized spectral-block
model plus a finite certificate imply the spectral gap. -/
theorem S05_Lem5_31_spectralGapFromBlockModelWithDim {n : Nat}
    (c : ℝ) (dim height : YoungDiagram n -> ℝ)
    (hmodel : SpectralBlockModelInputWithDim dim height)
    (hcert :
      ∀ lam : YoungDiagram n,
        ¬ IsOneRow lam -> ¬ IsStandard lam -> c * dim lam <= height lam) :
    MatchingSpectralGapConstant n c := by
  exact SpectralGapFromBlockModelWithDim c dim height hmodel hcert

end DictatorshipTesting
