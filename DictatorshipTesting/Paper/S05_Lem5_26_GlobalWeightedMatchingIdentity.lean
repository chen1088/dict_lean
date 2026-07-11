/-
Direct reverse imports:
- `DictatorshipTesting`
-/

import DictatorshipTesting.Paper.S05_Int_RegularYoungBlockDecomposition

/-!
Paper statement: Lemma 5.26 (`lem:global-weighted-matching-identity`).
-/

namespace DictatorshipTesting

theorem S05_Lem5_26_global_weighted_matching_identity_even
    (m : Nat)
    (action : ∀ lam : YoungDiagram (2 * (m + 1)),
      YoungOrthogonalActionData lam)
    (content : ∀ lam : YoungDiagram (2 * (m + 1)),
      JucysMurphyContentActionData (action lam))
    (hU1 : U1 (Fin (2 * (m + 1))) = concreteDegreeOneYoungBlockSum action)
    (hpos : ∀ lam : YoungDiagram (2 * (m + 1)), 0 < tableauDim lam)
    (F : Perm (Fin (2 * (m + 1))) → ℝ) :
    MatchingAverageScalarityInput F
      (concreteYoungBlockEnergy action content F)
      (fun lam => hEvenTableau (m + 1) lam / tableauDim lam) :=
  S05_matchingAverageScalarity_concrete_even m action content hU1 hpos F

theorem S05_Lem5_26_global_weighted_matching_identity_odd
    (m : Nat)
    (action : ∀ lam : YoungDiagram (2 * m + 1),
      YoungOrthogonalActionData lam)
    (content : ∀ lam : YoungDiagram (2 * m + 1),
      JucysMurphyContentActionData (action lam))
    (hU1 : U1 (Fin (2 * m + 1)) = concreteDegreeOneYoungBlockSum action)
    (hpos : ∀ lam : YoungDiagram (2 * m + 1), 0 < tableauDim lam)
    (F : Perm (Fin (2 * m + 1)) → ℝ) :
    MatchingAverageScalarityInput F
      (concreteYoungBlockEnergy action content F)
      (fun lam => hOddTableau m lam / tableauDim lam) :=
  S05_matchingAverageScalarity_concrete_odd m action content hU1 hpos F

end DictatorshipTesting
