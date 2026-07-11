import DictatorshipTesting.Paper.S05_Int_YoungOrthogonal

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.Defs.S05_IntDef_YoungOrthogonalActionData`
-/


/-!
Paper statement: Definition 5.5 (`def:content-adjacent-operators`)
Title in paper: Contents and adjacent operators.

Status: definition/interface. Paper-facing wrapper for contents, adjacent Young operators, and
diagonal content operators.
-/

noncomputable section

namespace DictatorshipTesting

/-- Definition 5.5 wrapper: content of a cell. -/
abbrev S05_Def5_05_cellContent {n : Nat} {lam : YoungDiagram n}
    (u : YoungCell lam) : Int :=
  YoungCell.content u

/-- Definition 5.5 wrapper: content of an entry in a tableau. -/
abbrev S05_Def5_05_entryContent {n : Nat} {lam : YoungDiagram n}
    (T : StandardYoungTableau lam) (a : Fin n) : Int :=
  entryContent T a

/-- Definition 5.5 wrapper: adjacent-transposition operator. -/
abbrev S05_Def5_05_youngAdjacentOperator {n : Nat}
    {lam : YoungDiagram (n + 1)} (a : Fin n) :=
  youngAdjacentOperator (lam := lam) a

/-- Definition 5.5 wrapper: diagonal content operator. -/
abbrev S05_Def5_05_diagonalContentOperator {n : Nat}
    {lam : YoungDiagram n} (a : Fin n) :=
  jucysMurphyDiagonalOperator (lam := lam) a

end DictatorshipTesting
