import AlgebraicLibrary.Young.TableauTrace
import DictatorshipTesting.Paper.Defs.S05_Def5_12c_AveragedHighMatchingElement
import Mathlib.LinearAlgebra.Trace

open AlgebraicLibrary

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_15_TraceOfOneLocalTruncationOnOneYoungBlock`
-/
/-!
Paper statement: Definition 5.12 part (d) `def:matching-idempotents`
Title in paper: Matching idempotents and averaged rejection.

The trace is defined explicitly as the sum of diagonal matrix coefficients in
the standard-tableau basis.  The accompanying lemmas prove the trace formula
for a scalar operator; no trace value is assumed as data.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- The matrix-coefficient-block trace of an operator acting on the right
tableau index.  The left tableau index is free and contributes one identical
copy of the tableau-space trace. -/
def youngBlockRightCoordinateTrace {n : Nat} {lam : YoungDiagram n}
    (op : TableauSpace lam -> TableauSpace lam) : Real :=
  ∑ _S : StandardYoungTableau lam,
    ∑ T : StandardYoungTableau lam, op (tableauBasisVec T) T

/-- The explicit tableau-coordinate trace agrees with the basis-independent
linear-map trace. -/
theorem tableauOperatorTrace_eq_linearMapTrace
    {n : Nat} {lam : YoungDiagram n}
    (op : TableauSpace lam →ₗ[Real] TableauSpace lam) :
    tableauOperatorTrace op = LinearMap.trace Real (TableauSpace lam) op := by
  classical
  rw [LinearMap.trace_eq_matrix_trace Real
    (Pi.basisFun Real (StandardYoungTableau lam))]
  unfold tableauOperatorTrace Matrix.trace
  apply Finset.sum_congr rfl
  intro T _hT
  change op (tableauBasisVec T) T =
    (LinearMap.toMatrix
      (Pi.basisFun Real (StandardYoungTableau lam))
      (Pi.basisFun Real (StandardYoungTableau lam)) op) T T
  rw [LinearMap.toMatrix_apply, Pi.basisFun_repr]
  have hbasis :
      Pi.basisFun Real (StandardYoungTableau lam) T = tableauBasisVec T := by
    funext S
    simp [Pi.basisFun_apply, Pi.single_apply, tableauBasisVec, eq_comm]
  rw [hbasis]

/-- If a supplied basis diagonalizes the matching cube with labels `label`,
then the trace of the actual represented high-matching element is the number
of high labels. This is the finite-dimensional trace step in Lemma 5.15; it
does not assume the trace value itself. -/
theorem fixedMatchingRejectionYoungOperator_trace_eq_highLabelCount_of_eigenbasis
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (n + 1))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι Real (TableauSpace lam))
    (label : ι -> Finset (Fin M.toOrdered.edgeCount))
    (heigen : forall i x,
      action.rep.rho (M.toOrdered.tau x) (b i) =
        cubeChar (label i) x • b i) :
    tableauOperatorTrace
        (S05_fixedMatchingRejectionYoungOperator action M) =
      ∑ i : ι,
        if S05_matchingCharacterHigh (label i) then (1 : Real) else 0 := by
  classical
  let op : TableauSpace lam →ₗ[Real] TableauSpace lam :=
    repOfGroupAlgebraElementLinearMap action.rep
      (S05_fixedMatchingHighElement M.toOrdered)
  change tableauOperatorTrace op = _
  rw [tableauOperatorTrace_eq_linearMapTrace op]
  rw [LinearMap.trace_eq_matrix_trace Real b]
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro i _hi
  change
    (LinearMap.toMatrix b b op) i i =
      if S05_matchingCharacterHigh (label i) then 1 else 0
  rw [LinearMap.toMatrix_apply]
  have hq := S05_fixedMatchingRejectionYoungOperator_apply_eigenvector
    action M (label i) (b i) (heigen i)
  change op (b i) =
    if S05_matchingCharacterHigh (label i) then b i else 0 at hq
  rw [hq]
  by_cases hhigh : S05_matchingCharacterHigh (label i)
  · simp [hhigh]
  · simp [hhigh]

/-- Trace is linear across a finite sum of tableau-coordinate operators. -/
theorem tableauOperatorTrace_finset_sum
    {n : Nat} {lam : YoungDiagram n} {ι : Type*}
    [DecidableEq ι]
    (s : Finset ι) (op : ι -> TableauSpace lam -> TableauSpace lam) :
    tableauOperatorTrace (fun f => ∑ i ∈ s, op i f) =
      ∑ i ∈ s, tableauOperatorTrace (op i) := by
  classical
  unfold tableauOperatorTrace
  calc
    (∑ T : StandardYoungTableau lam,
        (∑ i ∈ s, op i (tableauBasisVec T)) T) =
      ∑ T : StandardYoungTableau lam, ∑ i ∈ s,
        op i (tableauBasisVec T) T := by
      apply Finset.sum_congr rfl
      intro T _hT
      simp only [Finset.sum_apply]
    _ = ∑ i ∈ s, ∑ T : StandardYoungTableau lam,
        op i (tableauBasisVec T) T := by
      rw [Finset.sum_comm]

/-- Right action on a matrix-coefficient Young block has one copy for each
left tableau index, so its trace is `tableauDim` times the representation
trace. -/
theorem youngBlockTrace_eq_tableauDim_mul_repTrace
    {n : Nat} {lam : YoungDiagram n}
    (op : TableauSpace lam -> TableauSpace lam) :
    youngBlockRightCoordinateTrace op =
      tableauDim lam * tableauOperatorTrace op := by
  classical
  unfold youngBlockRightCoordinateTrace tableauOperatorTrace
  rw [Finset.sum_const]
  simp only [nsmul_eq_mul]
  rw [tableauDim, tableauDimNat_eq_card]
  norm_num

/-- The trace of one actual represented fixed high-matching operator is the
sum of the traces of its high-character Fourier idempotents. -/
theorem S05_fixedMatchingRejectionYoungOperator_trace_eq_sum_characters
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (n + 1)) :
    tableauOperatorTrace
        (S05_fixedMatchingRejectionYoungOperator action M) =
      ∑ R ∈ S05_matchingHighCharacterSet M.toOrdered,
        tableauOperatorTrace
          (S05_fixedMatchingCharacterYoungOperator action M R) := by
  classical
  calc
    tableauOperatorTrace
        (S05_fixedMatchingRejectionYoungOperator action M) =
      tableauOperatorTrace (fun f =>
        ∑ R ∈ S05_matchingHighCharacterSet M.toOrdered,
          S05_fixedMatchingCharacterYoungOperator action M R f) := by
      congr 1
      funext f
      exact S05_fixedMatchingRejectionYoungOperator_eq_sum_characters
        action M f
    _ = ∑ R ∈ S05_matchingHighCharacterSet M.toOrdered,
        tableauOperatorTrace
          (S05_fixedMatchingCharacterYoungOperator action M R) := by
      exact tableauOperatorTrace_finset_sum _ _

/-- On the full matrix-coefficient coordinate block, the fixed high-matching
trace acquires exactly the left-index factor `tableauDim`. -/
theorem fixedMatchingYoungBlockTrace_eq_tableauDim_mul_repTrace
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (n + 1)) :
    youngBlockRightCoordinateTrace
        (S05_fixedMatchingRejectionYoungOperator action M) =
      tableauDim lam *
        tableauOperatorTrace
          (S05_fixedMatchingRejectionYoungOperator action M) := by
  exact youngBlockTrace_eq_tableauDim_mul_repTrace _

/-- The concrete averaged rejection operator obtained from faithful Theorems 5.3 and 5.5
data has trace equal to its one-block scalar times the tableau dimension. -/
theorem S05_averagedRejectionYoungOperator_trace_eq_tableauDim_mul_scalar
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (content : JucysMurphyContentActionData action)
    (T0 : StandardYoungTableau lam) :
    tableauOperatorTrace
        (S05_averagedRejectionYoungOperatorData_from_section5
          action content).operator =
      tableauDim lam *
        (AveragedRejectionYoungOperatorData.toYoungModelOperatorCommutationData
          (S05_averagedRejectionYoungOperatorData_from_section5
            action content)).basisScalar T0 := by
  apply tableauOperatorTrace_eq_tableauDim_mul_of_scalar_on_basis
  intro T
  exact S05_averagedRejectionYoungOperator_scalar_from_section5
    action content T0 T

/-- The trace of the concrete averaged rejection operator is the finite
average of the traces of the represented fixed-matching high idempotents. -/
theorem S05_averagedRejectionYoungOperator_trace_eq_average_fixed
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (content : JucysMurphyContentActionData action) :
    tableauOperatorTrace
        (S05_averagedRejectionYoungOperatorData_from_section5
          action content).operator =
      (Fintype.card (NearPerfectMatching (n + 1)) : Real)⁻¹ *
        ∑ M : NearPerfectMatching (n + 1),
          tableauOperatorTrace
            (S05_fixedMatchingRejectionYoungOperator action M) := by
  classical
  unfold tableauOperatorTrace
  calc
    (∑ T : StandardYoungTableau lam,
      (S05_averagedRejectionYoungOperatorData_from_section5
        action content).operator (tableauBasisVec T) T) =
        ∑ T : StandardYoungTableau lam,
          (Fintype.card (NearPerfectMatching (n + 1)) : Real)⁻¹ *
            ∑ M : NearPerfectMatching (n + 1),
              S05_fixedMatchingRejectionYoungOperator action M
                (tableauBasisVec T) T := by
      apply Finset.sum_congr rfl
      intro T _hT
      change
        S05_averagedRejectionYoungOperator
            (YoungRepresentationActionData.ofYoungActions action content)
            (tableauBasisVec T) T =
          (Fintype.card (NearPerfectMatching (n + 1)) : Real)⁻¹ *
            ∑ M : NearPerfectMatching (n + 1),
              S05_fixedMatchingRejectionYoungOperator action M
                (tableauBasisVec T) T
      have h := congrFun
        (S05_averagedRejectionYoungOperator_eq_average_fixed
          action content (tableauBasisVec T)) T
      simpa only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul] using h
    _ = (Fintype.card (NearPerfectMatching (n + 1)) : Real)⁻¹ *
        ∑ T : StandardYoungTableau lam,
          ∑ M : NearPerfectMatching (n + 1),
            S05_fixedMatchingRejectionYoungOperator action M
              (tableauBasisVec T) T := by
      rw [Finset.mul_sum]
    _ = (Fintype.card (NearPerfectMatching (n + 1)) : Real)⁻¹ *
        ∑ M : NearPerfectMatching (n + 1),
          ∑ T : StandardYoungTableau lam,
            S05_fixedMatchingRejectionYoungOperator action M
              (tableauBasisVec T) T := by
      rw [Finset.sum_comm]

/-- With nonzero tableau dimension, the concrete one-block scalar is the
explicit tableau-coordinate trace divided by that dimension. -/
theorem S05_averagedRejectionYoungOperator_scalar_eq_trace_div_tableauDim
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (content : JucysMurphyContentActionData action)
    (T0 : StandardYoungTableau lam)
    (hdim : tableauDim lam ≠ 0) :
    (AveragedRejectionYoungOperatorData.toYoungModelOperatorCommutationData
        (S05_averagedRejectionYoungOperatorData_from_section5
          action content)).basisScalar T0 =
      tableauOperatorTrace
          (S05_averagedRejectionYoungOperatorData_from_section5
            action content).operator / tableauDim lam := by
  apply scalar_eq_tableauOperatorTrace_div_tableauDim _ _ hdim
  intro T
  exact S05_averagedRejectionYoungOperator_scalar_from_section5
    action content T0 T

end DictatorshipTesting
