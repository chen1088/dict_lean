import DictatorshipTesting.Paper.Defs.S05_IntDef_YoungCells

/-
Direct reverse imports:
- `DictatorshipTesting`
-/


/-!
Paper statement: Definition 5.1 (`def:young-diagrams-boxes`)
Title in paper: Young diagrams and boxes.

Status: definition/interface. Paper-facing wrapper for the elementary Young-diagram vocabulary used
throughout Section 5.
-/

noncomputable section

namespace DictatorshipTesting

/-- Definition 5.1 wrapper: Young diagrams of size `n`. -/
abbrev S05_Def5_01_YoungDiagram (n : Nat) := YoungDiagram n

/-- Definition 5.1 wrapper: zero-indexed row length. -/
abbrev S05_Def5_01_youngRow {n : Nat} (lam : YoungDiagram n) (i : Nat) : Nat :=
  youngRow lam i

/-- Definition 5.1 wrapper: cells of a Young diagram. -/
abbrev S05_Def5_01_youngCells {n : Nat} (lam : YoungDiagram n) :
    Finset (Fin n × Fin n) :=
  youngCells lam

end DictatorshipTesting
