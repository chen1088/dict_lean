import DictatorshipTesting.Paper.S05_Int_StandardYoungTableaux
import DictatorshipTesting.Paper.Defs.S05_Def5_01_YoungDiagramsAndBoxes

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.Defs.S05_Def5_04_TableauCoordinateSpace`
- `DictatorshipTesting.Paper.Defs.S05_Def5_09_OneBoxDeletionSpaces`
- `DictatorshipTesting.Paper.S05_Lem5_07_ConnectednessOfStandardTableaux`
- `DictatorshipTesting.Paper.S05_Lem5_13_SignedTwoBoxOrthogonalBranching`
-/


/-!
Paper statement: Definition 5.3 (`def:standard-tableaux`)
Title in paper: Standard Young tableaux and occupation notation.

Status: definition/interface. Paper-facing wrapper for standard tableaux and the box occupied by an
entry.
-/

noncomputable section

namespace DictatorshipTesting

/-- Definition 5.3 wrapper: standard Young tableaux of shape `lam`. -/
abbrev S05_Def5_03_StandardYoungTableau {n : Nat} (lam : YoungDiagram n) :=
  StandardYoungTableau lam

/-- Definition 5.3 wrapper: the cell occupied by entry `a`. -/
abbrev S05_Def5_03_cellOfEntry {n : Nat} {lam : YoungDiagram n}
    (T : StandardYoungTableau lam) (a : Fin n) :=
  cellOfEntry T a

/-- Definition 5.3 wrapper: the maximum entry lies in a given cell. -/
abbrev S05_Def5_03_TableauMaxAt {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (u : YoungCell lam) : Prop :=
  TableauMaxAt T u

end DictatorshipTesting
