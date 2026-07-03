import DictatorshipTesting.Paper.Defs

/-!
Paper statement: Definition 5.5
Title in paper: Two-box removals.

Status: re-exports the existing Young-diagram two-strip child predicates and
finite child sets used by the Section 5 finite certificates.
-/

noncomputable section

namespace DictatorshipTesting

/-- Horizontal two-box removals in the current finite Young-diagram model. -/
abbrev S05_IsHorizontalTwoBoxRemoval {n k : Nat}
    (lam : YoungDiagram n) (mu : YoungDiagram k) : Prop :=
  IsHorizontalTwoStripChild lam mu

/-- Vertical two-box removals in the current finite Young-diagram model. -/
abbrev S05_IsVerticalTwoBoxRemoval {n k : Nat}
    (lam : YoungDiagram n) (mu : YoungDiagram k) : Prop :=
  IsVerticalTwoStripChild lam mu

/-- Horizontal two-box children. -/
abbrev S05_horizontalTwoBoxChildren {n : Nat} (lam : YoungDiagram n) :=
  horizontalTwoStripChildren lam

/-- Vertical two-box children. -/
abbrev S05_verticalTwoBoxChildren {n : Nat} (lam : YoungDiagram n) :=
  verticalTwoStripChildren lam

end DictatorshipTesting
