import DictatorshipTesting.Paper.S05_Def5_05_TwoBoxRemovals

/-!
Paper statement: Definition 5.6
Title in paper: Signed two-box removals.

Status: paper-facing owner file for the rewritten Section 5 definition.  The
current finite scaffold records the two signed branches through horizontal and
vertical two-strip child sets; a fuller tableau-level signed-removal structure
will be added with the Specht/tableau formalization.
-/

noncomputable section

namespace DictatorshipTesting

/-- Positive signed branch: horizontal two-box removals. -/
abbrev S05_PositiveSignedTwoBoxRemoval {n k : Nat}
    (lam : YoungDiagram n) (mu : YoungDiagram k) : Prop :=
  S05_IsHorizontalTwoBoxRemoval lam mu

/-- Negative signed branch: vertical two-box removals. -/
abbrev S05_NegativeSignedTwoBoxRemoval {n k : Nat}
    (lam : YoungDiagram n) (mu : YoungDiagram k) : Prop :=
  S05_IsVerticalTwoBoxRemoval lam mu

/-- The positive signed branch has total row difference `2`. -/
theorem S05_Def5_06_sum_row_diff_of_positiveSignedTwoBoxRemoval
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : S05_PositiveSignedTwoBoxRemoval lam mu) :
    (Finset.range n).sum (fun i => youngRow lam i - youngRow mu i) = 2 := by
  exact S05_Def5_05_sum_row_diff_of_horizontalTwoBoxRemoval h

/-- The negative signed branch has total row difference `2`. -/
theorem S05_Def5_06_sum_row_diff_of_negativeSignedTwoBoxRemoval
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : S05_NegativeSignedTwoBoxRemoval lam mu) :
    (Finset.range n).sum (fun i => youngRow lam i - youngRow mu i) = 2 := by
  exact S05_Def5_05_sum_row_diff_of_verticalTwoBoxRemoval h

end DictatorshipTesting
