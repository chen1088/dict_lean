import DictatorshipTesting.Paper.S05_Int_SpectralBridgeRepresentationInputs
import DictatorshipTesting.Paper.Defs.AppA_DefA_01_YoungOrthogonalActionData

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.AppA_LemA_03_DegreeOneYoungBlockIdentification`
- `DictatorshipTesting.Paper.S05_Int_DegreeOneYoungBlock`
- `DictatorshipTesting.Paper.S05_Lem5_19_RegularYoungBlockDecomposition`
-/

/-!
# Concrete Young matrix-coefficient blocks

This internal file contains the reusable definitions needed to state the
faithful Appendix A.3 subspace identification without importing the full
regular-block decomposition.
-/

noncomputable section

namespace DictatorshipTesting

/-- The real matrix coefficient of a faithful Young action in the standard
tableau coordinate basis. -/
def youngMatrixCoefficient {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (S T : StandardYoungTableau lam) :
    Perm (Fin (n + 1)) -> Real :=
  fun pi =>
    tableauInner (tableauBasisVec S)
      (action.rep.rho pi (tableauBasisVec T))

/-- A finite linear combination of all matrix coefficients of one Young
action.  No injectivity, orthogonality, or spanning assertion is built into
this definition. -/
def youngBlockSynthesis {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (coeff : StandardYoungTableau lam × StandardYoungTableau lam -> Real) :
    Perm (Fin (n + 1)) -> Real :=
  fun pi =>
    ∑ ST : StandardYoungTableau lam × StandardYoungTableau lam,
      coeff ST * youngMatrixCoefficient action ST.1 ST.2 pi

/-- The concrete matrix-coefficient block of one supplied Young action. -/
def youngMatrixCoefficientBlock {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam) :
    Submodule Real (Perm (Fin (n + 1)) -> Real) :=
  Submodule.span Real
    (Set.range fun ST :
      StandardYoungTableau lam × StandardYoungTableau lam =>
        youngMatrixCoefficient action ST.1 ST.2)

/-- Every explicitly synthesized matrix-coefficient combination lies in the
concrete block span. -/
theorem youngBlockSynthesis_mem_youngMatrixCoefficientBlock
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (coeff : StandardYoungTableau lam × StandardYoungTableau lam -> Real) :
    youngBlockSynthesis action coeff ∈
      youngMatrixCoefficientBlock action := by
  classical
  have hsum :
      (∑ ST : StandardYoungTableau lam × StandardYoungTableau lam,
        coeff ST • youngMatrixCoefficient action ST.1 ST.2) ∈
          youngMatrixCoefficientBlock action := by
    apply Submodule.sum_mem
    intro ST _hST
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨ST, rfl⟩
  have hsynthesis :
      youngBlockSynthesis action coeff =
        ∑ ST : StandardYoungTableau lam × StandardYoungTableau lam,
          coeff ST • youngMatrixCoefficient action ST.1 ST.2 := by
    funext pi
    simp [youngBlockSynthesis, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsynthesis]
  exact hsum

/-- The concrete sum of the one-row and standard `(n-1,1)` Young blocks.
The supremum formulation also handles rank one, where there is no standard
block. -/
def concreteDegreeOneYoungBlockSum {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam) :
    Submodule Real (Perm (Fin (n + 1)) -> Real) :=
  ⨆ lam : YoungDiagram (n + 1),
    ⨆ (_h : IsOneRow lam ∨ IsStandard lam),
      youngMatrixCoefficientBlock (action lam)

/-- Each one-row or standard concrete block lies in their concrete sum. -/
theorem youngMatrixCoefficientBlock_le_concreteDegreeOneYoungBlockSum
    {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam)
    (lam : YoungDiagram (n + 1))
    (hlam : IsOneRow lam ∨ IsStandard lam) :
    youngMatrixCoefficientBlock (action lam) ≤
      concreteDegreeOneYoungBlockSum action := by
  exact le_iSup_of_le lam (le_iSup_of_le hlam le_rfl)

end DictatorshipTesting
