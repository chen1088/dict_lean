/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_08_RegularYoungBlockDecomposition`
- `DictatorshipTesting.Paper.S05_Prop5_16_AveragedRejectionOnYoungBlocks`
-/
import DictatorshipTesting.Paper.S05_Int_RegularYoungBlockDecomposition
import DictatorshipTesting.Paper.S05_Lem5_05_YoungBasisScalarCommutant
import DictatorshipTesting.Paper.S05_Thm5_03_JucysMurphyContentAction
import DictatorshipTesting.Paper.Defs.S05_Def5_06a_YoungBlock

/-!
Paper statement: Lemma 5.6 (`lem:young-matrix-coefficient-orthogonality`).

The complete same-shape and distinct-shape formulas are proved in the internal
regular Young-block assembly and re-exported here under the paper number.
-/

noncomputable section

namespace DictatorshipTesting

local instance {n : Nat} {lam : YoungDiagram (n + 1)} :
    DecidableEq (StandardYoungTableau lam) := Classical.decEq _

theorem S05_Lem5_06_same_shape
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (content : JucysMurphyContentActionData action)
    (S T U V : StandardYoungTableau lam) :
    permInner (youngMatrixCoefficient action S T)
        (youngMatrixCoefficient action U V) =
      if S = U ∧ T = V then 1 / tableauDim lam else 0 := by
  classical
  exact youngMatrixCoefficient_orthogonality_same_shape action content S T U V

theorem S05_Lem5_06_distinct_shapes
    {n : Nat} {lam mu : YoungDiagram (n + 1)}
    (hshape : lam ≠ mu)
    (actionLam : YoungOrthogonalActionData lam)
    (contentLam : JucysMurphyContentActionData actionLam)
    (actionMu : YoungOrthogonalActionData mu)
    (contentMu : JucysMurphyContentActionData actionMu)
    (S T : StandardYoungTableau lam)
    (U V : StandardYoungTableau mu) :
    permInner (youngMatrixCoefficient actionLam S T)
        (youngMatrixCoefficient actionMu U V) = 0 :=
  youngMatrixCoefficient_orthogonality_distinct_shapes hshape
    actionLam contentLam actionMu contentMu S T U V

end DictatorshipTesting
