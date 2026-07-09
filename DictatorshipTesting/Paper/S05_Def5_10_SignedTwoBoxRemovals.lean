import DictatorshipTesting.Paper.S05_Def5_09_TwoBoxRemovals

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_03_TwoBoxTableauBranching`
-/


/-!
Paper statement: Definition 5.10 (`def:signed-two-box-removals`)
Title in paper: Signed two-box removals.

Status: definition/interface. Paper-facing owner file for the rewritten Section 5 definition.  The
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
theorem S05_Def5_10_sum_row_diff_of_positiveSignedTwoBoxRemoval
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : S05_PositiveSignedTwoBoxRemoval lam mu) :
    (Finset.range n).sum (fun i => youngRow lam i - youngRow mu i) = 2 := by
  exact S05_Def5_09_sum_row_diff_of_horizontalTwoBoxRemoval h

/-- The negative signed branch has total row difference `2`. -/
theorem S05_Def5_10_sum_row_diff_of_negativeSignedTwoBoxRemoval
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : S05_NegativeSignedTwoBoxRemoval lam mu) :
    (Finset.range n).sum (fun i => youngRow lam i - youngRow mu i) = 2 := by
  exact S05_Def5_09_sum_row_diff_of_verticalTwoBoxRemoval h

/-- The positive signed branch is rowwise bounded by its parent. -/
theorem S05_Def5_10_row_le_parent_of_positiveSignedTwoBoxRemoval
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : S05_PositiveSignedTwoBoxRemoval lam mu) (i : Nat) :
    youngRow mu i <= youngRow lam i :=
  S05_Def5_09_row_le_parent_of_horizontalTwoBoxRemoval h i

/-- The negative signed branch is rowwise bounded by its parent. -/
theorem S05_Def5_10_row_le_parent_of_negativeSignedTwoBoxRemoval
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : S05_NegativeSignedTwoBoxRemoval lam mu) (i : Nat) :
    youngRow mu i <= youngRow lam i :=
  S05_Def5_09_row_le_parent_of_verticalTwoBoxRemoval h i

/-- Positive signed removals satisfy the horizontal two-strip row condition. -/
theorem S05_Def5_10_next_parent_row_le_child_row_of_positiveSignedTwoBoxRemoval
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : S05_PositiveSignedTwoBoxRemoval lam mu) (i : Nat) :
    youngRow lam (i + 1) <= youngRow mu i :=
  S05_Def5_09_next_parent_row_le_child_row_of_horizontalTwoBoxRemoval h i

/-- Negative signed removals satisfy the vertical two-strip row condition. -/
theorem S05_Def5_10_parent_row_le_child_row_add_one_of_negativeSignedTwoBoxRemoval
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : S05_NegativeSignedTwoBoxRemoval lam mu) (i : Nat) :
    youngRow lam i <= youngRow mu i + 1 :=
  S05_Def5_09_parent_row_le_child_row_add_one_of_verticalTwoBoxRemoval h i

/-- In a negative signed removal, each row loses at most one box. -/
theorem S05_Def5_10_row_diff_le_one_of_negativeSignedTwoBoxRemoval
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : S05_NegativeSignedTwoBoxRemoval lam mu) (i : Nat) :
    youngRow lam i - youngRow mu i <= 1 :=
  S05_Def5_09_row_diff_le_one_of_verticalTwoBoxRemoval h i

end DictatorshipTesting
