import DictatorshipTesting.Paper.S05_Int_TableauDimension
import DictatorshipTesting.Paper.S05_Int_YoungOrthogonal
import DictatorshipTesting.Paper.Defs.S05_Def5_03_StandardTableaux

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.Defs.S05_Def5_05_ContentAndAdjacentOperators`
- `DictatorshipTesting.Paper.Defs.S05_Def5_12d_TableauOperatorTrace`
- `DictatorshipTesting.Paper.S05_Int_RegularYoungBlockDecomposition`
-/
/-!
Paper statement: Definition 5.4 (`def:tableau-coordinate-space`)
Title in paper: Tableau coordinate space.

Status: definition/interface. Paper-facing wrapper for the tableau-count dimension and coordinate
space used by the Young-basis operator model.
-/

noncomputable section

namespace DictatorshipTesting

/-- Definition 5.4 wrapper: tableau-count dimension. -/
abbrev S05_Def5_04_tableauDim {n : Nat} (lam : YoungDiagram n) : ℝ :=
  tableauDim lam

/-- Definition 5.4 wrapper: coordinate space with basis indexed by tableaux. -/
abbrev S05_Def5_04_TableauSpace {n : Nat} (lam : YoungDiagram n) :=
  TableauSpace lam

/-- Definition 5.4 wrapper: coordinate basis vector. -/
abbrev S05_Def5_04_tableauBasisVec {n : Nat} {lam : YoungDiagram n}
    (T : StandardYoungTableau lam) :=
  tableauBasisVec T


/-- Trace of an operator on a tableau coordinate space, computed in the
standard-tableau basis. -/
def tableauOperatorTrace {n : Nat} {lam : YoungDiagram n}
    (op : TableauSpace lam -> TableauSpace lam) : Real :=
  ∑ T : StandardYoungTableau lam, op (tableauBasisVec T) T


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


end DictatorshipTesting
