import DictatorshipTesting.Paper.Aux_YoungDiagramCorners

/-!
Paper statement: Definition 5.2 (`def:removable-corners`)
Title in paper: Removable corners and one-box removals.

Status: paper-facing wrapper for subdiagrams, one-box children, and removable
row/corner vocabulary.
-/

noncomputable section

namespace DictatorshipTesting

/-- Definition 5.2 wrapper: Young subdiagram predicate. -/
abbrev S05_Def5_02_IsYoungSubdiagram {n k : Nat}
    (mu : YoungDiagram k) (lam : YoungDiagram n) : Prop :=
  IsYoungSubdiagram mu lam

/-- Definition 5.2 wrapper: one-box child predicate. -/
abbrev S05_Def5_02_IsOneBoxChild {n k : Nat}
    (lam : YoungDiagram n) (mu : YoungDiagram k) : Prop :=
  IsOneBoxChild lam mu

/-- Definition 5.2 wrapper: finite set of one-box children. -/
abbrev S05_Def5_02_oneBoxChildren {n : Nat} (lam : YoungDiagram n) :=
  oneBoxChildren lam

/-- Definition 5.2 wrapper: removable row predicate. -/
abbrev S05_Def5_02_IsRemovableRow {n : Nat}
    (lam : YoungDiagram n) (r : Nat) : Prop :=
  IsRemovableRow lam r

end DictatorshipTesting
