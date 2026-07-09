import DictatorshipTesting.Paper.Aux_SpectralBridgeRepresentationInputs
import DictatorshipTesting.Paper.Aux_SpectralBridgeFromCertificates
import DictatorshipTesting.Paper.S05_Lem5_16_BlockScalarOfTheAveragedRejection
import DictatorshipTesting.Paper.Aux_TableauDimension

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S05_Lem5_17_BlockLowerBoundImpliesTheGap`
- `DictatorshipTesting.Paper.S05_Lem5_19_EvenSpectralBridge`
- `DictatorshipTesting.Paper.S05_Lem5_20_OddSpectralBridge`
-/


/-!
# Dimension-parameterized spectral bridge interfaces

The original `youngDim` spectral bridge uses `youngDim` as the block-dimension
function.  This helper keeps the same energy, `U_1`, and scalarity vocabulary,
but makes the trace/scalar formulas parametric in an arbitrary dimension
function `dim`.

This file does not assert any representation-theoretic spectral model.  It only
defines the parameterized interface used by later algebraic wrappers.
-/

noncomputable section

namespace DictatorshipTesting

/-- The trace/scalar formula plus a finite certificate inequality gives a lower
bound on the scalar of each non-`U_1` block, for any positive dimension
function. -/
theorem blockScalar_lower_bound_of_traceScalarFormula_withDim {n : Nat}
    {dim height theta : YoungDiagram n -> ℝ} {c : ℝ}
    (htraceScalar : TraceScalarValueInputWithDim dim height theta)
    (hcert :
      ∀ lam : YoungDiagram n,
        ¬ IsOneRow lam -> ¬ IsStandard lam -> c * dim lam <= height lam) :
    ∀ lam ∈ nonU1YoungBlocks n, c <= theta lam := by
  classical
  intro lam hlam
  have hnot_row : ¬ IsOneRow lam := (Finset.mem_filter.mp hlam).2.1
  have hnot_std : ¬ IsStandard lam := (Finset.mem_filter.mp hlam).2.2
  rcases htraceScalar lam with ⟨hdim_pos, htheta⟩
  rw [htheta]
  exact (le_div_iff₀ hdim_pos).mpr (hcert lam hnot_row hnot_std)

/-- Dimension positivity plus the parameterized block trace identity imply the
parameterized trace/scalar value formula. -/
theorem traceScalarValue_of_blockTraceIdentity_withDim {n : Nat}
    {dim height theta : YoungDiagram n -> ℝ}
    (hdim : YoungDimensionPositiveInputWithDim dim)
    (htrace : BlockTraceIdentityInputWithDim dim height theta) :
    TraceScalarValueInputWithDim dim height theta := by
  intro lam
  have hpos : 0 < dim lam := hdim lam
  exact ⟨hpos,
    centralizationBridge_scalar_eq_trace_div_dimension
      (dim lam) (height lam) (theta lam) (ne_of_gt hpos) (htrace lam)⟩

/-- Convert a parameterized scalarity-plus-trace package into the scalar-value
package used by the spectral-gap wrapper. -/
def matchingAverageScalarModel_of_blockTraceModel_withDim {n : Nat}
    {dim height : YoungDiagram n -> ℝ} {F : Perm (Fin n) -> ℝ}
    {blockEnergy : YoungDiagram n -> ℝ}
    (hdim : YoungDimensionPositiveInputWithDim dim)
    (model : MatchingAverageBlockTraceModelWithDim dim height F blockEnergy) :
    MatchingAverageScalarModelWithDim dim height F blockEnergy where
  theta := model.theta
  scalarity := model.scalarity
  trace_value :=
    traceScalarValue_of_blockTraceIdentity_withDim hdim model.trace_identity

/-- Spectral gap from a scalar trace formula and a finite certificate, for an
arbitrary block-dimension function. -/
theorem SpectralGapFromBlockScalarsWithDim {n : Nat} (c : ℝ)
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
  exact
    SpectralGapFromBlockScalars c F blockEnergy theta
      hdecomp hu1 hscalarity
      (blockScalar_lower_bound_of_traceScalarFormula_withDim htrace hcert)

/-- Spectral gap from a dimension-parameterized spectral-block model and a
finite certificate.  The representation-theoretic model remains an explicit
hypothesis. -/
theorem SpectralGapFromBlockModelWithDim {n : Nat}
    (c : ℝ) (dim height : YoungDiagram n -> ℝ)
    (hmodel : SpectralBlockModelInputWithDim dim height)
    (hcert :
      ∀ lam : YoungDiagram n,
        ¬ IsOneRow lam -> ¬ IsStandard lam -> c * dim lam <= height lam) :
    MatchingSpectralGapConstant n c := by
  intro F
  rcases hmodel F with ⟨energy, ⟨scalar⟩⟩
  exact
    SpectralGapFromBlockScalarsWithDim c F dim height
      energy.blockEnergy scalar.theta energy.nonneg energy.u1_identification
      scalar.scalarity scalar.trace_value hcert

end DictatorshipTesting
