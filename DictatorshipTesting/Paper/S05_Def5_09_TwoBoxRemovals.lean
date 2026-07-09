import DictatorshipTesting.Paper.Aux_YoungDiagramCorners

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Def5_10_SignedTwoBoxRemovals`
-/


/-!
Paper statement: Definition 5.9 (`def:two-box-removals`)
Title in paper: Two-box removals.

Status: definition/interface. Re-exports the existing Young-diagram two-strip child predicates and
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

/-- Definition 5.7 row fact: a horizontal two-box removal has total row
difference `2`. -/
theorem S05_Def5_09_sum_row_diff_of_horizontalTwoBoxRemoval
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : S05_IsHorizontalTwoBoxRemoval lam mu) :
    (Finset.range n).sum (fun i => youngRow lam i - youngRow mu i) = 2 := by
  exact sum_row_diff_of_horizontalTwoStripChild h

/-- Definition 5.7 row fact: a vertical two-box removal has total row
difference `2`. -/
theorem S05_Def5_09_sum_row_diff_of_verticalTwoBoxRemoval
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : S05_IsVerticalTwoBoxRemoval lam mu) :
    (Finset.range n).sum (fun i => youngRow lam i - youngRow mu i) = 2 := by
  exact sum_row_diff_of_verticalTwoStripChild h

/-- Definition 5.7 row fact: horizontal two-box children are rowwise bounded by
their parent. -/
theorem S05_Def5_09_row_le_parent_of_horizontalTwoBoxRemoval
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : S05_IsHorizontalTwoBoxRemoval lam mu) (i : Nat) :
    youngRow mu i <= youngRow lam i :=
  row_le_parent_of_horizontalTwoStripChild h i

/-- Definition 5.7 row fact: vertical two-box children are rowwise bounded by
their parent. -/
theorem S05_Def5_09_row_le_parent_of_verticalTwoBoxRemoval
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : S05_IsVerticalTwoBoxRemoval lam mu) (i : Nat) :
    youngRow mu i <= youngRow lam i :=
  row_le_parent_of_verticalTwoStripChild h i

/-- Definition 5.7 horizontal two-strip row condition. -/
theorem S05_Def5_09_next_parent_row_le_child_row_of_horizontalTwoBoxRemoval
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : S05_IsHorizontalTwoBoxRemoval lam mu) (i : Nat) :
    youngRow lam (i + 1) <= youngRow mu i :=
  next_parent_row_le_child_row_of_horizontalTwoStripChild h i

/-- Definition 5.7 vertical two-strip row condition. -/
theorem S05_Def5_09_parent_row_le_child_row_add_one_of_verticalTwoBoxRemoval
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : S05_IsVerticalTwoBoxRemoval lam mu) (i : Nat) :
    youngRow lam i <= youngRow mu i + 1 :=
  parent_row_le_child_row_add_one_of_verticalTwoStripChild h i

/-- Definition 5.7 row fact: in a vertical two-box removal, every row loses at
most one box. -/
theorem S05_Def5_09_row_diff_le_one_of_verticalTwoBoxRemoval
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : S05_IsVerticalTwoBoxRemoval lam mu) (i : Nat) :
    youngRow lam i - youngRow mu i <= 1 :=
  row_diff_le_one_of_verticalTwoStripChild h i

end DictatorshipTesting
