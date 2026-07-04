import DictatorshipTesting.Paper.Aux_SpectralBridgeRepresentationInputs
import DictatorshipTesting.Paper.S05_Lem5_26_BlockScalarOfTheAveragedRejection
import DictatorshipTesting.Paper.Aux_TableauDimension

/-!
# Dimension-parameterized spectral bridge interfaces

The legacy Section 5 spectral bridge uses `youngDim` as the block-dimension
function.  This helper keeps the same energy, `U_1`, and scalarity vocabulary,
but makes the trace/scalar formulas parametric in an arbitrary dimension
function `dim`.

This file does not assert any representation-theoretic spectral model.  It only
defines the parameterized interface used by later algebraic wrappers.
-/

noncomputable section

namespace DictatorshipTesting

/-- Positivity of an arbitrary Young-block dimension function. -/
def YoungDimensionPositiveInputWithDim {n : Nat}
    (dim : YoungDiagram n -> ℝ) : Prop :=
  ∀ lam : YoungDiagram n, 0 < dim lam

/-- Trace/scalar value using an arbitrary Young-block dimension function. -/
def TraceScalarValueInputWithDim {n : Nat}
    (dim height theta : YoungDiagram n -> ℝ) : Prop :=
  ∀ lam : YoungDiagram n, 0 < dim lam ∧ theta lam = height lam / dim lam

/-- Block trace identity before dividing by an arbitrary Young-block dimension. -/
def BlockTraceIdentityInputWithDim {n : Nat}
    (dim height theta : YoungDiagram n -> ℝ) : Prop :=
  ∀ lam : YoungDiagram n,
    dim lam ^ (2 : Nat) * theta lam = dim lam * height lam

/-- Matching-average scalar model with a parameterized block dimension. -/
structure MatchingAverageScalarModelWithDim {n : Nat}
    (dim height : YoungDiagram n -> ℝ)
    (F : Perm (Fin n) -> ℝ)
    (blockEnergy : YoungDiagram n -> ℝ) where
  theta : YoungDiagram n -> ℝ
  scalarity : MatchingAverageScalarityInput F blockEnergy theta
  trace_value : TraceScalarValueInputWithDim dim height theta

/-- Scalarity plus the block trace identity before dividing by a parameterized
block dimension. -/
structure MatchingAverageBlockTraceModelWithDim {n : Nat}
    (dim height : YoungDiagram n -> ℝ)
    (F : Perm (Fin n) -> ℝ)
    (blockEnergy : YoungDiagram n -> ℝ) where
  theta : YoungDiagram n -> ℝ
  scalarity : MatchingAverageScalarityInput F blockEnergy theta
  trace_identity : BlockTraceIdentityInputWithDim dim height theta

/-- A compact parameterized spectral-block model.  The decomposition,
`U_1`-identification, and scalarity predicates are the same as in the legacy
interface; only the scalar trace value is dimension-parametric. -/
def SpectralBlockModelInputWithDim {n : Nat}
    (dim height : YoungDiagram n -> ℝ) : Prop :=
  ∀ F : Perm (Fin n) -> ℝ,
    ∃ energy : YoungBlockEnergyModel F,
      Nonempty
        (MatchingAverageScalarModelWithDim dim height F energy.blockEnergy)

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

end DictatorshipTesting
