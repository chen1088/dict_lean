import AlgebraicLibrary.Young.JucysMurphyContentAction
import DictatorshipTesting.Paper.S05_Lem5_01_AdjacentTranspositionsInYoungsBasis
import DictatorshipTesting.Paper.S05_Thm5_02_YoungOrthogonalAction

open AlgebraicLibrary

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Int_RegularYoungBlockDecomposition`
- `DictatorshipTesting.Paper.S05_Lem5_04_ContentSeparationAndTableauConnectivity`
- `DictatorshipTesting.Paper.S05_Lem5_06_YoungMatrixCoefficientOrthogonality`
-/

/-!
# Theorem 5.3: Jucys--Murphy content action

The coefficient-function and tableau-content recurrences are included with the
paper theorem they prove.
-/

noncomputable section

namespace DictatorshipTesting

/-- Group-algebra coefficient form of the Jucys--Murphy recurrence. -/
theorem S05_Thm5_03_jucysMurphyElement_succ_recurrence
    {n : Nat} (a : Fin n) (g : Perm (Fin (n + 1))) :
    s05_jucysMurphyElement a.succ g =
      s05_jucysMurphyElement a.castSucc
          (s05_adjacentTransposition a * g * s05_adjacentTransposition a) +
        if g = s05_adjacentTransposition a then 1 else 0 :=
  s05_jucysMurphyElement_succ_recurrence a g

/-- Tableau-operator form of the same recurrence. -/
theorem S05_Thm5_03_tableauContent_succ_recurrence
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (a : Fin n) (f : TableauSpace lam) :
    jucysMurphyDiagonalOperator a.succ f =
      youngAdjacentOperator a
          (jucysMurphyDiagonalOperator a.castSucc
            (youngAdjacentOperator a f)) +
        youngAdjacentOperator a f :=
  (youngAdjacent_content_succ_recurrence a f).symm

/-- Theorem 5.3: every concrete Young orthogonal action carries the faithful
Jucys--Murphy content action. -/
theorem S05_Thm5_03_jucysMurphyContentAction
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam) :
    Nonempty (JucysMurphyContentActionData action) := by
  exact jucysMurphyContentActionData_nonempty action

end DictatorshipTesting
