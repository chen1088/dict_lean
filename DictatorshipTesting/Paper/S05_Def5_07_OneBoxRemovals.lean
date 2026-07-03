import DictatorshipTesting.Paper.Defs

/-!
Paper statement: Definition 5.7
Title in paper: One-box removals.

Status: re-exports the existing one-box child predicate and finite child sets.
-/

noncomputable section

namespace DictatorshipTesting

/-- One-box removals in the current finite Young-diagram model. -/
abbrev S05_IsOneBoxRemoval {n k : Nat}
    (lam : YoungDiagram n) (mu : YoungDiagram k) : Prop :=
  IsOneBoxChild lam mu

/-- One-box children. -/
abbrev S05_oneBoxChildren {n : Nat} (lam : YoungDiagram n) :=
  oneBoxChildren lam

/-- Odd one-box children used by the Section 5 finite certificate. -/
abbrev S05_oneBoxChildrenOdd (m : Nat)
    (lam : YoungDiagram (2 * m + 1)) :=
  oneBoxChildrenOdd m lam

end DictatorshipTesting
