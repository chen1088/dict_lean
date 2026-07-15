/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_09_DegreeOneYoungBlockIdentification`
- `DictatorshipTesting.Paper.S05_Prop5_16_AveragedRejectionOnYoungBlocks`
-/
import DictatorshipTesting.Paper.S05_Int_RegularYoungBlockDecomposition
import DictatorshipTesting.Paper.S05_Lem5_06_YoungMatrixCoefficientOrthogonality
import DictatorshipTesting.Paper.S05_Lem5_07_YoungTableauSumOfSquares
import DictatorshipTesting.Paper.Defs.S05_IntDef_YoungBlockEnergyProfile
import AlgebraicLibrary.Young.IndexedDiagram

open AlgebraicLibrary

/-!
Paper statement: Lemma 5.8 (`lem:regular-young-block-decomposition`).
-/

namespace DictatorshipTesting

theorem S05_Lem5_08_globalYoungMatrixCoefficient_linearIndependent
    {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam)
    (content : ∀ lam : YoungDiagram (n + 1),
      JucysMurphyContentActionData (action lam)) :
    LinearIndependent ℝ (globalYoungMatrixCoefficient action) :=
  globalYoungMatrixCoefficient_linearIndependent action content

theorem S05_Lem5_08_globalYoungMatrixCoefficient_span_all
    {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam)
    (content : ∀ lam : YoungDiagram (n + 1),
      JucysMurphyContentActionData (action lam)) :
    Submodule.span ℝ (Set.range (globalYoungMatrixCoefficient action)) = ⊤ :=
  globalYoungMatrixCoefficient_span_all action content

theorem S05_Lem5_08_sum_concreteYoungBlockComponent
    {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam)
    (content : ∀ lam : YoungDiagram (n + 1),
      JucysMurphyContentActionData (action lam))
    (F : Perm (Fin (n + 1)) → ℝ) :
    (∑ lam : YoungDiagram (n + 1),
      concreteYoungBlockComponent action content F lam) = F :=
  sum_concreteYoungBlockComponent action content F

theorem S05_Lem5_08_parseval
    {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam)
    (content : ∀ lam : YoungDiagram (n + 1),
      JucysMurphyContentActionData (action lam))
    (F : Perm (Fin (n + 1)) → ℝ) :
    permInner F F = ∑ lam : YoungDiagram (n + 1),
      concreteYoungBlockEnergy action content F lam :=
  permInner_self_eq_sum_concreteYoungBlockEnergy action content F


/-- Lemma 5.8 model projection: each Young-block energy is nonnegative. -/
theorem S05_Lem5_08_blockEnergy_nonnegative {n : Nat}
    {F : Perm (Fin n) → ℝ}
    (energy : YoungBlockEnergyModel F)
    (lam : YoungDiagram n) :
    0 ≤ energy.blockEnergy lam :=
  energy.nonneg lam

/-- Lemma 5.8 model projection: the distance to `U_1` is the sum of all
non-`U_1` Young-block energies. -/
theorem S05_Lem5_08_u1_identification {n : Nat}
    {F : Perm (Fin n) → ℝ}
    (energy : YoungBlockEnergyModel F) :
    l2DistSqToU1 F =
      (nonU1YoungBlocks n).sum energy.blockEnergy :=
  energy.u1_identification


end DictatorshipTesting
