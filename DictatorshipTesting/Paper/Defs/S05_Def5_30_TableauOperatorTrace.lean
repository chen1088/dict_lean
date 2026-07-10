import DictatorshipTesting.Paper.Defs.S05_Def5_04_TableauCoordinateSpace
import DictatorshipTesting.Paper.Defs.S05_Def5_29_AveragedHighMatchingElement

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_12_TraceOfOneLocalTruncationOnOneYoungBlock`
-/

/-!
Paper statement: Definition 5.30 (`def:tableau-operator-trace`)
Title in paper: Tableau-coordinate operator trace.

The trace is defined explicitly as the sum of diagonal matrix coefficients in
the standard-tableau basis.  The accompanying lemmas prove the trace formula
for a scalar operator; no trace value is assumed as data.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Trace of an operator on a tableau coordinate space, computed in the
standard-tableau basis. -/
def tableauOperatorTrace {n : Nat} {lam : YoungDiagram n}
    (op : TableauSpace lam -> TableauSpace lam) : Real :=
  ∑ T : StandardYoungTableau lam, op (tableauBasisVec T) T

/-- The matrix-coefficient-block trace of an operator acting on the right
tableau index.  The left tableau index is free and contributes one identical
copy of the tableau-space trace. -/
def youngBlockRightCoordinateTrace {n : Nat} {lam : YoungDiagram n}
    (op : TableauSpace lam -> TableauSpace lam) : Real :=
  ∑ _S : StandardYoungTableau lam,
    ∑ T : StandardYoungTableau lam, op (tableauBasisVec T) T

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

/-- A scalar operator on the tableau basis has trace equal to the tableau
dimension times its scalar. -/
theorem tableauOperatorTrace_eq_tableauDim_mul_of_scalar_on_basis
    {n : Nat} {lam : YoungDiagram n}
    (op : TableauSpace lam -> TableauSpace lam) (c : Real)
    (hscalar :
      ∀ T : StandardYoungTableau lam,
        op (tableauBasisVec T) =
          fun U => c * tableauBasisVec T U) :
    tableauOperatorTrace op = tableauDim lam * c := by
  classical
  unfold tableauOperatorTrace
  calc
    (∑ T : StandardYoungTableau lam, op (tableauBasisVec T) T) =
        ∑ _T : StandardYoungTableau lam, c := by
      apply Finset.sum_congr rfl
      intro T _hT
      rw [hscalar T]
      simp [tableauBasisVec]
    _ = (Fintype.card (StandardYoungTableau lam) : Real) * c := by
      simp
    _ = tableauDim lam * c := by
      rw [tableauDim, tableauDimNat_eq_card]

/-- If the tableau dimension is nonzero, the scalar of a scalar-on-basis
operator is its trace divided by the tableau dimension. -/
theorem scalar_eq_tableauOperatorTrace_div_tableauDim
    {n : Nat} {lam : YoungDiagram n}
    (op : TableauSpace lam -> TableauSpace lam) (c : Real)
    (hdim : tableauDim lam ≠ 0)
    (hscalar :
      ∀ T : StandardYoungTableau lam,
        op (tableauBasisVec T) =
          fun U => c * tableauBasisVec T U) :
    c = tableauOperatorTrace op / tableauDim lam := by
  rw [tableauOperatorTrace_eq_tableauDim_mul_of_scalar_on_basis op c hscalar]
  field_simp

/-- The concrete averaged rejection operator obtained from faithful A.1/A.2
data has trace equal to its one-block scalar times the tableau dimension. -/
theorem S05_averagedRejectionYoungOperator_trace_eq_tableauDim_mul_scalar
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (hconn : External.AppendixA.StandardTableauxSwapConnectedStatement)
    (action : YoungOrthogonalActionData lam)
    (content : JucysMurphyContentActionData action)
    (T0 : StandardYoungTableau lam) :
    tableauOperatorTrace
        (S05_averagedRejectionYoungOperatorData_from_appendixA
          action content).operator =
      tableauDim lam *
        (AveragedRejectionYoungOperatorData.toYoungModelOperatorCommutationData
          (S05_averagedRejectionYoungOperatorData_from_appendixA
            action content)).basisScalar T0 := by
  apply tableauOperatorTrace_eq_tableauDim_mul_of_scalar_on_basis
  intro T
  exact S05_averagedRejectionYoungOperator_scalar_from_appendixA
    hconn action content T0 T

/-- The trace of the concrete averaged rejection operator is the finite
average of the traces of the represented fixed-matching high idempotents. -/
theorem S05_averagedRejectionYoungOperator_trace_eq_average_fixed
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (content : JucysMurphyContentActionData action) :
    tableauOperatorTrace
        (S05_averagedRejectionYoungOperatorData_from_appendixA
          action content).operator =
      (Fintype.card (NearPerfectMatching (n + 1)) : Real)⁻¹ *
        ∑ M : NearPerfectMatching (n + 1),
          tableauOperatorTrace
            (S05_fixedMatchingRejectionYoungOperator action M) := by
  classical
  unfold tableauOperatorTrace
  calc
    (∑ T : StandardYoungTableau lam,
      (S05_averagedRejectionYoungOperatorData_from_appendixA
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
            (YoungRepresentationActionData.ofAppendixA action content)
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
    (hconn : External.AppendixA.StandardTableauxSwapConnectedStatement)
    (action : YoungOrthogonalActionData lam)
    (content : JucysMurphyContentActionData action)
    (T0 : StandardYoungTableau lam)
    (hdim : tableauDim lam ≠ 0) :
    (AveragedRejectionYoungOperatorData.toYoungModelOperatorCommutationData
        (S05_averagedRejectionYoungOperatorData_from_appendixA
          action content)).basisScalar T0 =
      tableauOperatorTrace
          (S05_averagedRejectionYoungOperatorData_from_appendixA
            action content).operator / tableauDim lam := by
  apply scalar_eq_tableauOperatorTrace_div_tableauDim _ _ hdim
  intro T
  exact S05_averagedRejectionYoungOperator_scalar_from_appendixA
    hconn action content T0 T

end DictatorshipTesting
