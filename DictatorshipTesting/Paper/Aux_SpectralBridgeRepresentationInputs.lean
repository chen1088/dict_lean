import DictatorshipTesting.Paper.Defs

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.AppA_ThmA_01_YoungOrthogonalRealization`
- `DictatorshipTesting.Paper.Aux_SpectralBridgeDimensionParam`
- `DictatorshipTesting.Paper.Aux_SpectralBridgeFromCertificates`
- `DictatorshipTesting.Paper.S05_Def5_08_YoungBlock`
- `DictatorshipTesting.Paper.S05_Lem5_29_YoungBasisScalarCommutant`
- `DictatorshipTesting.Paper.S05_Lem5_32_RegularYoungBlockDecomposition`
-/


/-!
# Spectral bridge representation inputs

This file contains compatibility interface objects for the original `youngDim`
spectral bridge.  The current paper route uses the dimension-parametric
`tableauDim` bridge in Lemmas 5.31--5.34.
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

/-- Nonnegative squared energies for each Young block.  This is the numerical
shadow of orthogonality of the regular Young decomposition. -/
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

/-- Positivity of Young-block dimensions. -/
def YoungDimensionPositiveInput (n : ℕ) : Prop :=
  ∀ lam : YoungDiagram n, 0 < youngDim lam

/-- Trace identity for the scalar on a Young block.  Since the corresponding
regular-representation block has dimension `d_lambda^2`, scalarity plus the
local trace formula gives `d_lambda^2 * theta_lambda = d_lambda * h`. -/
def BlockTraceIdentityInput {n : ℕ}
    (height theta : YoungDiagram n → ℝ) : Prop :=
  ∀ lam : YoungDiagram n,
    youngDim lam ^ (2 : ℕ) * theta lam = youngDim lam * height lam

/-- Trace/scalar value supplied by the local trace calculation and division by
the block dimension: `theta_lambda = h(lambda)/d_lambda`.  Positivity of
`d_lambda` is included because the scalar formula divides by that dimension. -/
def TraceScalarValueInput {n : ℕ}
    (height theta : YoungDiagram n → ℝ) : Prop :=
  ∀ lam : YoungDiagram n,
    0 < youngDim lam ∧ theta lam = height lam / youngDim lam

/-- Young-block energies for a fixed function, together with the identification
of the `U_1`-orthogonal energy. -/
structure YoungBlockEnergyModel {n : ℕ} (F : Perm (Fin n) → ℝ) where
  blockEnergy : YoungDiagram n → ℝ
  nonneg : YoungBlockDecompositionInput blockEnergy
  u1_identification : U1YoungBlockIdentificationInput F blockEnergy

/-- Scalar model for the averaged matching projection on the Young blocks.  The
first field is Schur-lemma scalarity of the matching average; the second field
is the trace/scalar value calculation. -/
structure MatchingAverageScalarModel {n : ℕ}
    (height : YoungDiagram n → ℝ) (F : Perm (Fin n) → ℝ)
    (blockEnergy : YoungDiagram n → ℝ) where
  theta : YoungDiagram n → ℝ
  scalarity : MatchingAverageScalarityInput F blockEnergy theta
  trace_value : TraceScalarValueInput height theta

/-- Scalarity and block-trace identity before dividing by the block dimension.
This is closer to the representation-theoretic output: Schur's lemma supplies a
scalar on each block, and the local trace computation identifies its trace. -/
structure MatchingAverageBlockTraceModel {n : ℕ}
    (height : YoungDiagram n → ℝ) (F : Perm (Fin n) → ℝ)
    (blockEnergy : YoungDiagram n → ℝ) where
  theta : YoungDiagram n → ℝ
  scalarity : MatchingAverageScalarityInput F blockEnergy theta
  trace_identity : BlockTraceIdentityInput height theta

/-- A compact package of the representation-theoretic block model used by the
algebraic spectral-gap wrapper. -/
def SpectralBlockModelInput {n : ℕ}
    (height : YoungDiagram n → ℝ) : Prop :=
  ∀ F : Perm (Fin n) → ℝ,
    ∃ energy : YoungBlockEnergyModel F,
      Nonempty (MatchingAverageScalarModel height F energy.blockEnergy)

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
`U_1`-identification, and scalarity predicates are the same as in the original
interface; only the scalar trace value is dimension-parametric. -/
def SpectralBlockModelInputWithDim {n : Nat}
    (dim height : YoungDiagram n -> ℝ) : Prop :=
  ∀ F : Perm (Fin n) -> ℝ,
    ∃ energy : YoungBlockEnergyModel F,
      Nonempty
        (MatchingAverageScalarModelWithDim dim height F energy.blockEnergy)

end DictatorshipTesting
