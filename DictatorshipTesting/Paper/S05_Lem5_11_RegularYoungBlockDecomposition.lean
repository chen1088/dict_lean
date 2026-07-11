/-
Direct reverse imports:
- `DictatorshipTesting`
-/

import DictatorshipTesting.Paper.S05_Int_RegularYoungBlockDecomposition

/-!
Paper statement: Lemma 5.11 (`lem:regular-young-block-decomposition`).
-/

namespace DictatorshipTesting

theorem S05_Lem5_11_globalYoungMatrixCoefficient_linearIndependent
    {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam)
    (content : ∀ lam : YoungDiagram (n + 1),
      JucysMurphyContentActionData (action lam)) :
    LinearIndependent ℝ (globalYoungMatrixCoefficient action) :=
  globalYoungMatrixCoefficient_linearIndependent action content

theorem S05_Lem5_11_globalYoungMatrixCoefficient_span_all
    {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam)
    (content : ∀ lam : YoungDiagram (n + 1),
      JucysMurphyContentActionData (action lam)) :
    Submodule.span ℝ (Set.range (globalYoungMatrixCoefficient action)) = ⊤ :=
  globalYoungMatrixCoefficient_span_all action content

theorem S05_Lem5_11_sum_concreteYoungBlockComponent
    {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam)
    (content : ∀ lam : YoungDiagram (n + 1),
      JucysMurphyContentActionData (action lam))
    (F : Perm (Fin (n + 1)) → ℝ) :
    (∑ lam : YoungDiagram (n + 1),
      concreteYoungBlockComponent action content F lam) = F :=
  sum_concreteYoungBlockComponent action content F

theorem S05_Lem5_11_parseval
    {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam)
    (content : ∀ lam : YoungDiagram (n + 1),
      JucysMurphyContentActionData (action lam))
    (F : Perm (Fin (n + 1)) → ℝ) :
    permInner F F = ∑ lam : YoungDiagram (n + 1),
      concreteYoungBlockEnergy action content F lam :=
  permInner_self_eq_sum_concreteYoungBlockEnergy action content F

end DictatorshipTesting
