/-
Direct reverse imports:
- `DictatorshipTesting`
-/

import DictatorshipTesting.Paper.S05_Int_JucysMurphyContentAction

/-!
Paper statement: Lemma 5.4 (`lem:jucys-murphy-recurrence`).
-/

namespace DictatorshipTesting

/-- Group-algebra coefficient form of the Jucys--Murphy recurrence. -/
theorem S05_Lem5_04_jucysMurphyElement_succ_recurrence
    {n : Nat} (a : Fin n) (g : Perm (Fin (n + 1))) :
    s05_jucysMurphyElement a.succ g =
      s05_jucysMurphyElement a.castSucc
          (s05_adjacentTransposition a * g * s05_adjacentTransposition a) +
        if g = s05_adjacentTransposition a then 1 else 0 :=
  s05_jucysMurphyElement_succ_recurrence a g

/-- Tableau-operator form of the same recurrence. -/
theorem S05_Lem5_04_tableauContent_succ_recurrence
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (a : Fin n) (f : TableauSpace lam) :
    jucysMurphyDiagonalOperator a.succ f =
      youngAdjacentOperator a
          (jucysMurphyDiagonalOperator a.castSucc
            (youngAdjacentOperator a f)) +
        youngAdjacentOperator a f :=
  (youngAdjacent_content_succ_recurrence a f).symm

end DictatorshipTesting
