import DictatorshipTesting.Paper.S05_Int_StandardYoungTableaux
import DictatorshipTesting.Paper.S05_Int_OneBoxDeletionIntertwining
import DictatorshipTesting.Paper.S05_Int_OneBoxDeletionUnitary
import DictatorshipTesting.Paper.S05_Lem5_01_AdjacentTranspositionsInYoungsBasis
import DictatorshipTesting.Paper.Defs.S05_Def5_07a_TwoBoxRemovals
import DictatorshipTesting.Paper.Defs.S05_Def5_09_OneBoxDeletionSpaces

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_15_BranchingDimensionsAndSignPatternCardinalities`
- `DictatorshipTesting.Paper.S05_Lem5_16_MatchingSubgroupEigenbasis`
-/


/-!
Paper statement: Lemma 5.14 (`lem:one-box-corner-decomposition`)
Title in paper: One-box decomposition and deletion.

The row combinatorics, deletion isometry, and earlier-swap intertwining are
proved in the imported internal modules and exposed together here.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.14 row-form component: a one-box child differs from its parent in
exactly one row. -/
theorem S05_oneBox_row_form
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : IsOneBoxChild lam mu) :
    exists r : Nat,
      youngRow lam r = youngRow mu r + 1 ∧
      forall s : Nat, s ≠ r -> youngRow lam s = youngRow mu s := by
  exact exists_unique_row_of_oneBoxChild h

/-- Lemma 5.14 unique-row component. -/
theorem S05_oneBox_row_form_unique
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : IsOneBoxChild lam mu) :
    ∃! r : Nat,
      youngRow lam r = youngRow mu r + 1 ∧
      forall s : Nat, s ≠ r -> youngRow lam s = youngRow mu s := by
  exact existsUnique_row_of_oneBoxChild h

/-- Lemma 5.14 removable-row component. -/
theorem S05_oneBox_removable_row
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : IsOneBoxChild lam mu) :
    exists r : Nat,
      IsRemovableRow lam r ∧
      youngRow lam r = youngRow mu r + 1 ∧
      forall s : Nat, s ≠ r -> youngRow lam s = youngRow mu s := by
  exact exists_removableRow_of_oneBoxChild h

/-- Lemma 5.14 removable-corner component. -/
theorem S05_oneBox_removable_corner
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : IsOneBoxChild lam mu) :
    exists u : Nat × Nat,
      IsRemovableCornerBox lam u ∧
      u.2 = youngRow mu u.1 ∧
      youngRow lam u.1 = youngRow mu u.1 + 1 ∧
      forall s : Nat, s ≠ u.1 -> youngRow lam s = youngRow mu s := by
  exact exists_removableCornerBox_of_oneBoxChild h

/-- Lemma 5.14 tableau component: the maximum entry lies in a removable corner. -/
theorem S05_oneBox_tableau_max_removable_corner {n : Nat}
    {lam : YoungDiagram (n + 1)} (T : StandardYoungTableau lam)
    {u : YoungCell lam} (hu : TableauMaxAt T u) :
    IsRemovableCornerBox lam (YoungCell.toNatPair u) := by
  exact removableCornerBox_of_tableauMaxAt T hu

/-- Lemma 5.14 tableau component: the maximum entry lies in a unique removable
corner. -/
theorem S05_oneBox_tableau_unique_removable_corner {n : Nat}
    {lam : YoungDiagram (n + 1)} (T : StandardYoungTableau lam) :
    ∃! u : YoungCell lam,
      TableauMaxAt T u ∧ IsRemovableCornerBox lam (YoungCell.toNatPair u) := by
  exact existsUnique_removableCornerBox_tableauMaxAt T

/-- Lemma 5.14 row-form component, paper-numbered name. -/
theorem S05_Lem5_14_row_form
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : IsOneBoxChild lam mu) :
    exists r : Nat,
      youngRow lam r = youngRow mu r + 1 ∧
      forall s : Nat, s ≠ r -> youngRow lam s = youngRow mu s := by
  exact S05_oneBox_row_form h

/-- Lemma 5.14 unique-row component, paper-numbered name. -/
theorem S05_Lem5_14_row_form_unique
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : IsOneBoxChild lam mu) :
    ∃! r : Nat,
      youngRow lam r = youngRow mu r + 1 ∧
      forall s : Nat, s ≠ r -> youngRow lam s = youngRow mu s := by
  exact S05_oneBox_row_form_unique h

/-- Lemma 5.14 removable-row component, paper-numbered name. -/
theorem S05_Lem5_14_removable_row
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : IsOneBoxChild lam mu) :
    exists r : Nat,
      IsRemovableRow lam r ∧
      youngRow lam r = youngRow mu r + 1 ∧
      forall s : Nat, s ≠ r -> youngRow lam s = youngRow mu s := by
  exact S05_oneBox_removable_row h

/-- Lemma 5.14 removable-corner component, paper-numbered name. -/
theorem S05_Lem5_14_removable_corner
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : IsOneBoxChild lam mu) :
    exists u : Nat × Nat,
      IsRemovableCornerBox lam u ∧
      u.2 = youngRow mu u.1 ∧
      youngRow lam u.1 = youngRow mu u.1 + 1 ∧
      forall s : Nat, s ≠ u.1 -> youngRow lam s = youngRow mu s := by
  exact S05_oneBox_removable_corner h

/-- Lemma 5.14 cell component, paper-numbered name: parent cells are child cells
or the deleted cell. -/
theorem S05_Lem5_14_parent_cell_iff_child_cell_or_deleted
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : IsOneBoxChild lam mu) {r s c : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t) :
    c < youngRow lam s <->
      c < youngRow mu s ∨ (s = r ∧ c = youngRow mu r) := by
  exact parent_cell_iff_child_cell_or_deleted_of_oneBoxChild_row h hr

/-- Lemma 5.14 cell component, paper-numbered name: child cells are parent cells
except the deleted cell. -/
theorem S05_Lem5_14_child_cell_iff_parent_cell_not_deleted
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : IsOneBoxChild lam mu) {r s c : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t) :
    c < youngRow mu s <->
      c < youngRow lam s ∧ ¬ (s = r ∧ c = youngRow mu r) := by
  exact child_cell_iff_parent_cell_not_deleted_of_oneBoxChild_row h hr

/-- Lemma 5.14 tableau component, paper-numbered name. -/
theorem S05_Lem5_14_tableau_max_removable_corner {n : Nat}
    {lam : YoungDiagram (n + 1)} (T : StandardYoungTableau lam)
    {u : YoungCell lam} (hu : TableauMaxAt T u) :
    IsRemovableCornerBox lam (YoungCell.toNatPair u) := by
  exact S05_oneBox_tableau_max_removable_corner T hu

/-- Lemma 5.14 tableau component, paper-numbered unique-corner name. -/
theorem S05_Lem5_14_tableau_unique_removable_corner {n : Nat}
    {lam : YoungDiagram (n + 1)} (T : StandardYoungTableau lam) :
    ∃! u : YoungCell lam,
      TableauMaxAt T u ∧ IsRemovableCornerBox lam (YoungCell.toNatPair u) := by
  exact S05_oneBox_tableau_unique_removable_corner T

/-- Lemma 5.14(a): deleting the maximum entry is a bijection on the remaining
tableau cells. -/
theorem S05_Lem5_14_deleteMaxEntry_bijective {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) {u : YoungCell lam}
    (hu : TableauMaxAt T u) :
    Function.Bijective (tableauDeleteMaxEntry T hu) :=
  S05_oneBoxDeletion_deleteMaxEntry_bijective T hu

/-- Lemma 5.14(b): deletion preserves the coordinate inner product. -/
theorem S05_Lem5_14_deletionCoordinateMap_inner
    {n : Nat} {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      ∀ t : Nat, t ≠ r → youngRow lam t = youngRow mu t)
    (f g : S05_oneBoxDeletion_OneBoxDeletionCoordinateSpace h hr) :
    tableauInner
        (S05_oneBoxDeletion_deletionCoordinateMap h hr f)
        (S05_oneBoxDeletion_deletionCoordinateMap h hr g) =
      S05_oneBoxDeletion_oneBoxDeletionInner h hr f g :=
  S05_oneBoxDeletion_deletionCoordinateMap_inner h hr f g

/-- Lemma 5.14(c): deletion intertwines every earlier adjacent operator. -/
theorem S05_Lem5_14_deletionCoordinateMap_youngAdjacentOperator_intertwines
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      ∀ t : Nat, t ≠ r → youngRow lam t = youngRow mu t)
    (a : Fin n)
    (f : S05_oneBoxDeletion_OneBoxDeletionCoordinateSpace h hr) :
    youngAdjacentOperator a
        (S05_oneBoxDeletion_deletionCoordinateMap h hr f) =
      S05_oneBoxDeletion_deletionCoordinateMap h hr
        (S05_oneBoxIntertwining_deletionFiberYoungAdjacentOperator h hr a f) :=
  S05_oneBoxIntertwining_deletionCoordinateMap_youngAdjacentOperator_intertwines
    h hr a f

end DictatorshipTesting
