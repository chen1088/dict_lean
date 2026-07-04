import DictatorshipTesting.Paper.Aux_SpectralBridgeRepresentationInputs
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

end DictatorshipTesting
