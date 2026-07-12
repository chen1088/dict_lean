import DictatorshipTesting.Paper.S05_Lem5_06_DiagonalContentEigenspaces
import DictatorshipTesting.Paper.S05_Int_SpectralBridgeRepresentationInputs
import DictatorshipTesting.Paper.Defs.S05_IntDef_YoungBasisScalarCommutantInput
import DictatorshipTesting.Paper.S05_Lem5_07_ConnectednessOfStandardTableaux

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.Defs.S05_Def5_12b_GroupAlgebraAction`
- `DictatorshipTesting.Paper.S05_Int_RegularYoungBlockDecomposition`
- `DictatorshipTesting.Paper.S05_Lem5_09_YoungMatrixCoefficientOrthogonality`
- `DictatorshipTesting.Paper.S05_Lem5_21_BlockScalarOfTheAveragedRejection`
-/


/-!
Paper statement: Lemma 5.8 (`lem:young-basis-scalar-commutant`)
Title in paper: Young-basis scalar commutant.

Status: proven.  The generic scalar commutant is proved here; Definition 5.12
applies it to the actual averaged high-matching element for every supplied
Young representation action model.
-/

noncomputable section

namespace DictatorshipTesting

/-- A concrete operator on one tableau-coordinate Young block, together with
the linearity and commutation properties needed for the Young-basis scalar
commutant argument.  This is narrower than matching-average scalarity: it is a
single-block operator interface and says nothing about matchings or block
energies. -/
structure YoungModelOperatorCommutationData {n : Nat}
    (lam : YoungDiagram (n + 1)) where
  op : TableauSpace lam -> TableauSpace lam
  map_add :
    ∀ f g : TableauSpace lam,
      op (fun T => f T + g T) = fun T => op f T + op g T
  map_smul :
    ∀ (c : ℝ) (f : TableauSpace lam),
      op (fun T => c * f T) = fun T => c * op f T
  commutes_adjacent :
    ∀ (a : Fin n) (f : TableauSpace lam),
      op (youngAdjacentOperator a f) =
        youngAdjacentOperator a (op f)
  commutes_content :
    ∀ (a : Fin (n + 1)) (f : TableauSpace lam),
      op (jucysMurphyDiagonalOperator a f) =
        jucysMurphyDiagonalOperator a (op f)

/-- The scalar coefficient seen by a concrete block operator on a tableau basis
vector. -/
def YoungModelOperatorCommutationData.basisScalar {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (data : YoungModelOperatorCommutationData lam)
    (T : StandardYoungTableau lam) : ℝ :=
  data.op (tableauBasisVec T) T

/-- Commutation with all diagonal content operators forces the image of each
tableau basis vector to stay on the same basis line. -/
theorem YoungModelOperatorCommutationData.op_basis_eq_smul_basis {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (data : YoungModelOperatorCommutationData lam)
    (T : StandardYoungTableau lam) :
    data.op (tableauBasisVec T) =
      fun U => data.basisScalar T * tableauBasisVec T U := by
  apply diagonalContent_commonEigenvector_eq_smul_basis T
  intro a
  rw [← data.commutes_content a (tableauBasisVec T)]
  rw [jucysMurphyDiagonalOperator_basis_eigen T a]
  exact data.map_smul (entryContent T a : ℝ) (tableauBasisVec T)

/-- Along one valid adjacent-tableau swap, a concrete block operator commuting
with the adjacent Young operator has the same basis scalar on both endpoints. -/
theorem YoungModelOperatorCommutationData.basisScalar_eq_of_adjacent {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (data : YoungModelOperatorCommutationData lam)
    {T U : StandardYoungTableau lam}
    (hstep : StandardTableauxAdjacent (lam := lam) T U) :
    data.basisScalar T = data.basisScalar U := by
  classical
  rcases hstep with ⟨a, hrow, hcol, rfl⟩
  let U : StandardYoungTableau lam := adjacentSwapTableau T a hrow hcol
  let d : ℝ := youngAdjacentDiagCoeff T a
  let o : ℝ := youngAdjacentOffCoeff T a
  have hUT : U ≠ T := by
    simpa [U] using adjacentSwapTableau_ne_self T a hrow hcol
  have hopT := data.op_basis_eq_smul_basis T
  have hopU := data.op_basis_eq_smul_basis U
  have hSa :
      youngAdjacentOperator a (tableauBasisVec T) =
        fun S => d * tableauBasisVec T S + o * tableauBasisVec U S := by
    simpa [U, d, o] using
      youngAdjacentOperator_basis_swappable_eq T a hrow hcol
  have hleft :
      data.op (youngAdjacentOperator a (tableauBasisVec T)) U =
        o * data.basisScalar U := by
    rw [hSa]
    rw [data.map_add]
    rw [data.map_smul, data.map_smul]
    have hTcoord :
        data.op (tableauBasisVec T) U = 0 := by
      have hcoord := congrFun hopT U
      simpa [YoungModelOperatorCommutationData.basisScalar, tableauBasisVec,
        hUT] using hcoord
    have hUcoord :
        data.op (tableauBasisVec U) U = data.basisScalar U := rfl
    simp [hTcoord, hUcoord, o]
  have hright :
      youngAdjacentOperator a (data.op (tableauBasisVec T)) U =
        o * data.basisScalar T := by
    rw [hopT]
    rw [youngAdjacentOperator_smul]
    have hswap :
        youngAdjacentOperator a (tableauBasisVec T) U = o := by
      simpa [U, o] using
        youngAdjacentOperator_basis_swappable_swap_value T a hrow hcol
    simp [hswap]
    ring
  have hcomm :=
    congrFun (data.commutes_adjacent a (tableauBasisVec T)) U
  have ho : o ≠ 0 := by
    simpa [o] using youngAdjacentOffCoeff_ne_zero_of_swappable T a hrow hcol
  rw [hleft, hright] at hcomm
  exact (mul_left_cancel₀ ho hcomm).symm

/-- A concrete block operator commuting with every adjacent Young operator and
every diagonal content operator has a constant basis scalar on the whole block.
The path is supplied internally by Lemma 5.3. -/
theorem YoungModelOperatorCommutationData.basisScalar_constant {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (data : YoungModelOperatorCommutationData lam)
    (T U : StandardYoungTableau lam) :
    data.basisScalar T = data.basisScalar U := by
  have hpath := S05_Lem5_07_standardTableauxSwapConnectedness lam T U
  induction hpath with
  | refl =>
      rfl
  | tail hpath hstep ih =>
      exact ih.trans (data.basisScalar_eq_of_adjacent hstep)

/-- A paper-facing generic scalar commutant wrapper: once a concrete operator
on a Young block is known to commute with content and adjacent Young operators,
the internally proved Lemma 5.3 makes it scalar on every tableau basis vector.
This does not instantiate the averaged matching rejection operator. -/
theorem S05_Lem5_08_youngModelOperator_scalar_on_basis {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (data : YoungModelOperatorCommutationData lam)
    (T0 T : StandardYoungTableau lam) :
    data.op (tableauBasisVec T) =
      fun U => data.basisScalar T0 * tableauBasisVec T U := by
  rw [data.op_basis_eq_smul_basis T]
  have hscalar := data.basisScalar_constant T T0
  rw [hscalar]

/-- Lemma 5.8 interface projection: if the scalar commutant input holds, then
the averaged rejection is the weighted sum of block energies. -/
theorem S05_Lem5_08_matchingAverageScalarity_eq_sum {n : Nat}
    {F : Perm (Fin n) → ℝ}
    {blockEnergy theta : YoungDiagram n → ℝ}
    (h : S05_IntDef_YoungBasisScalarCommutantInput F blockEnergy theta) :
    matchingMeanProjectionError F =
      (nonU1YoungBlocks n).sum (fun lam => theta lam * blockEnergy lam) := by
  exact h

end DictatorshipTesting
