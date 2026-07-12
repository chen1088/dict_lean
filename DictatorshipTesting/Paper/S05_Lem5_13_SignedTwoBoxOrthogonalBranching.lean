import DictatorshipTesting.Paper.Defs.S05_Def5_07b_SignedTwoBoxRemovals
import DictatorshipTesting.Paper.S05_Int_TableauDimension
import DictatorshipTesting.Paper.S05_Int_OneBoxDeletionUnitary
import DictatorshipTesting.Paper.S05_Int_OneBoxDeletionIntertwining
import DictatorshipTesting.Paper.Defs.S05_Def5_07a_TwoBoxRemovals
import DictatorshipTesting.Paper.Defs.S05_Def5_03_StandardTableaux

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.Defs.S05_Def5_08_SignedTwoBoxExtensionSpaces`
- `DictatorshipTesting.Paper.S05_Lem5_15_BranchingDimensionsAndSignPatternCardinalities`
- `DictatorshipTesting.Paper.S05_Lem5_16_MatchingSubgroupEigenbasis`
-/


/-!
Paper statement: Lemma 5.13 (`lem:two-box-tableau-branching`)
Title in paper: Signed two-box orthogonal branching.

Status: proven. Proved below as a concrete set-level tableau branching statement for a
fixed two-step deletion pattern, with content/row/column preservation wrappers.
No Specht-module branching theorem is asserted here.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.4 set-level component: perform the first one-box deletion in an
iterated two-box tableau deletion. -/
def S05_Lem5_13_deleteFirstMaxAsTableau
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (T : StandardYoungTableau lam)
    (hu : TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h hr)) :
    StandardYoungTableau mu :=
  deleteMaxAsStandardYoungTableauOfOneBoxChildRow
    h hr
    (deletedCornerCellOfOneBoxChildRow h hr)
    (deletedCornerCell_row h hr)
    (deletedCornerCell_col h hr)
    T hu

/-- Lemma 5.4 set-level component: the first deleted cell is a removable corner
of the parent tableau shape. -/
theorem S05_Lem5_13_first_deleted_cell_removable_corner
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (T : StandardYoungTableau lam)
    (hu : TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h hr)) :
    IsRemovableCornerBox lam
      (YoungCell.toNatPair (deletedCornerCellOfOneBoxChildRow h hr)) := by
  exact removableCornerBox_of_tableauMaxAt T hu

/-- Lemma 5.4 set-level component: after deleting the largest entry, the new
largest entry lies in a unique removable corner of the child shape. -/
theorem S05_Lem5_13_after_first_deletion_unique_second_corner
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (T : StandardYoungTableau lam)
    (hu : TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h hr)) :
    ∃! v : YoungCell mu,
      TableauMaxAt (S05_Lem5_13_deleteFirstMaxAsTableau h hr T hu) v ∧
        IsRemovableCornerBox mu (YoungCell.toNatPair v) := by
  exact existsUnique_removableCornerBox_tableauMaxAt
    (S05_Lem5_13_deleteFirstMaxAsTableau h hr T hu)

/-- Lemma 5.4 set-level component: any second maximum-entry cell after the first
deletion is a removable corner of the child shape. -/
theorem S05_Lem5_13_second_deleted_cell_removable_corner
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (T : StandardYoungTableau lam)
    (hu : TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h hr))
    {v : YoungCell mu}
    (hv : TableauMaxAt (S05_Lem5_13_deleteFirstMaxAsTableau h hr T hu) v) :
    IsRemovableCornerBox mu (YoungCell.toNatPair v) := by
  exact removableCornerBox_of_tableauMaxAt
    (S05_Lem5_13_deleteFirstMaxAsTableau h hr T hu) hv

/-- Lemma 5.4 basis-level component: the first deletion in the two-box
branching step preserves the content sequence on the remaining entries. -/
theorem S05_Lem5_13_first_deletion_tableauContentSequence
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (T : StandardYoungTableau lam)
    (hu : TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h hr))
    (a : Fin (n + 1)) :
    tableauContentSequence (S05_Lem5_13_deleteFirstMaxAsTableau h hr T hu) a =
      tableauContentSequence T (Fin.castSucc a) := by
  exact S05_oneBoxIntertwining_deleteMax_tableauContentSequence
    h hr (deletedCornerCellOfOneBoxChildRow h hr)
    (deletedCornerCell_row h hr) (deletedCornerCell_col h hr) T hu a

/-- Lemma 5.4 basis-level component: after the first deletion, the child cell
containing a remaining entry maps back to the original parent cell. -/
theorem S05_Lem5_13_first_deletion_childCellToParent_cellOfEntry
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (T : StandardYoungTableau lam)
    (hu : TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h hr))
    (a : Fin (n + 1)) :
    childCellToParentCellOfOneBoxChildRow h hr
      (cellOfEntry (S05_Lem5_13_deleteFirstMaxAsTableau h hr T hu) a)
      =
    cellOfEntry T (Fin.castSucc a) := by
  exact S05_oneBoxIntertwining_childCellToParent_cellOfEntry_deleteMax
    h hr (deletedCornerCellOfOneBoxChildRow h hr)
    (deletedCornerCell_row h hr) (deletedCornerCell_col h hr) T hu a

/-- Lemma 5.4 basis-level component: the first deletion preserves the row of
each remaining entry. -/
theorem S05_Lem5_13_first_deletion_cellOfEntry_row
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (T : StandardYoungTableau lam)
    (hu : TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h hr))
    (a : Fin (n + 1)) :
    YoungCell.row
      (cellOfEntry (S05_Lem5_13_deleteFirstMaxAsTableau h hr T hu) a)
      =
    YoungCell.row (cellOfEntry T (Fin.castSucc a)) := by
  exact S05_oneBoxIntertwining_deleteMax_cellOfEntry_row
    h hr (deletedCornerCellOfOneBoxChildRow h hr)
    (deletedCornerCell_row h hr) (deletedCornerCell_col h hr) T hu a

/-- Lemma 5.4 basis-level component: the first deletion preserves the column of
each remaining entry. -/
theorem S05_Lem5_13_first_deletion_cellOfEntry_col
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (T : StandardYoungTableau lam)
    (hu : TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h hr))
    (a : Fin (n + 1)) :
    YoungCell.col
      (cellOfEntry (S05_Lem5_13_deleteFirstMaxAsTableau h hr T hu) a)
      =
    YoungCell.col (cellOfEntry T (Fin.castSucc a)) := by
  exact S05_oneBoxIntertwining_deleteMax_cellOfEntry_col
    h hr (deletedCornerCellOfOneBoxChildRow h hr)
    (deletedCornerCell_row h hr) (deletedCornerCell_col h hr) T hu a

/-- Lemma 5.4 set-level component: perform the second one-box deletion after
the first one in an iterated two-box tableau deletion. -/
def S05_Lem5_13_deleteSecondMaxAsTableau
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)} {nu : YoungDiagram n}
    (h₁ : IsOneBoxChild lam mu) {r₁ : Nat}
    (hr₁ :
      youngRow lam r₁ = youngRow mu r₁ + 1 ∧
      forall t : Nat, t ≠ r₁ -> youngRow lam t = youngRow mu t)
    (h₂ : IsOneBoxChild mu nu) {r₂ : Nat}
    (hr₂ :
      youngRow mu r₂ = youngRow nu r₂ + 1 ∧
      forall t : Nat, t ≠ r₂ -> youngRow mu t = youngRow nu t)
    (T : StandardYoungTableau lam)
    (hu₁ : TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h₁ hr₁))
    (hu₂ :
      TableauMaxAt (S05_Lem5_13_deleteFirstMaxAsTableau h₁ hr₁ T hu₁)
        (deletedCornerCellOfOneBoxChildRow h₂ hr₂)) :
    StandardYoungTableau nu :=
  deleteMaxAsStandardYoungTableauOfOneBoxChildRow
    h₂ hr₂
    (deletedCornerCellOfOneBoxChildRow h₂ hr₂)
    (deletedCornerCell_row h₂ hr₂)
    (deletedCornerCell_col h₂ hr₂)
    (S05_Lem5_13_deleteFirstMaxAsTableau h₁ hr₁ T hu₁) hu₂

/-- Lemma 5.4 basis-level component: the second deletion preserves the content
sequence on entries remaining after that deletion. -/
theorem S05_Lem5_13_second_deletion_tableauContentSequence
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)} {nu : YoungDiagram n}
    (h₁ : IsOneBoxChild lam mu) {r₁ : Nat}
    (hr₁ :
      youngRow lam r₁ = youngRow mu r₁ + 1 ∧
      forall t : Nat, t ≠ r₁ -> youngRow lam t = youngRow mu t)
    (h₂ : IsOneBoxChild mu nu) {r₂ : Nat}
    (hr₂ :
      youngRow mu r₂ = youngRow nu r₂ + 1 ∧
      forall t : Nat, t ≠ r₂ -> youngRow mu t = youngRow nu t)
    (T : StandardYoungTableau lam)
    (hu₁ : TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h₁ hr₁))
    (hu₂ :
      TableauMaxAt (S05_Lem5_13_deleteFirstMaxAsTableau h₁ hr₁ T hu₁)
        (deletedCornerCellOfOneBoxChildRow h₂ hr₂))
    (a : Fin n) :
    tableauContentSequence
        (S05_Lem5_13_deleteSecondMaxAsTableau h₁ hr₁ h₂ hr₂ T hu₁ hu₂) a
      =
    tableauContentSequence
        (S05_Lem5_13_deleteFirstMaxAsTableau h₁ hr₁ T hu₁) (Fin.castSucc a) := by
  exact S05_oneBoxIntertwining_deleteMax_tableauContentSequence
    h₂ hr₂ (deletedCornerCellOfOneBoxChildRow h₂ hr₂)
    (deletedCornerCell_row h₂ hr₂) (deletedCornerCell_col h₂ hr₂)
    (S05_Lem5_13_deleteFirstMaxAsTableau h₁ hr₁ T hu₁) hu₂ a

/-- Lemma 5.4 basis-level component: after the second deletion, the child cell
containing a remaining entry maps back to its cell after the first deletion. -/
theorem S05_Lem5_13_second_deletion_childCellToParent_cellOfEntry
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)} {nu : YoungDiagram n}
    (h₁ : IsOneBoxChild lam mu) {r₁ : Nat}
    (hr₁ :
      youngRow lam r₁ = youngRow mu r₁ + 1 ∧
      forall t : Nat, t ≠ r₁ -> youngRow lam t = youngRow mu t)
    (h₂ : IsOneBoxChild mu nu) {r₂ : Nat}
    (hr₂ :
      youngRow mu r₂ = youngRow nu r₂ + 1 ∧
      forall t : Nat, t ≠ r₂ -> youngRow mu t = youngRow nu t)
    (T : StandardYoungTableau lam)
    (hu₁ : TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h₁ hr₁))
    (hu₂ :
      TableauMaxAt (S05_Lem5_13_deleteFirstMaxAsTableau h₁ hr₁ T hu₁)
        (deletedCornerCellOfOneBoxChildRow h₂ hr₂))
    (a : Fin n) :
    childCellToParentCellOfOneBoxChildRow h₂ hr₂
      (cellOfEntry
        (S05_Lem5_13_deleteSecondMaxAsTableau h₁ hr₁ h₂ hr₂ T hu₁ hu₂) a)
      =
    cellOfEntry
      (S05_Lem5_13_deleteFirstMaxAsTableau h₁ hr₁ T hu₁) (Fin.castSucc a) := by
  exact S05_oneBoxIntertwining_childCellToParent_cellOfEntry_deleteMax
    h₂ hr₂ (deletedCornerCellOfOneBoxChildRow h₂ hr₂)
    (deletedCornerCell_row h₂ hr₂) (deletedCornerCell_col h₂ hr₂)
    (S05_Lem5_13_deleteFirstMaxAsTableau h₁ hr₁ T hu₁) hu₂ a

/-- Lemma 5.4 basis-level component: the second deletion preserves rows relative
to the first-deleted tableau. -/
theorem S05_Lem5_13_second_deletion_cellOfEntry_row
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)} {nu : YoungDiagram n}
    (h₁ : IsOneBoxChild lam mu) {r₁ : Nat}
    (hr₁ :
      youngRow lam r₁ = youngRow mu r₁ + 1 ∧
      forall t : Nat, t ≠ r₁ -> youngRow lam t = youngRow mu t)
    (h₂ : IsOneBoxChild mu nu) {r₂ : Nat}
    (hr₂ :
      youngRow mu r₂ = youngRow nu r₂ + 1 ∧
      forall t : Nat, t ≠ r₂ -> youngRow mu t = youngRow nu t)
    (T : StandardYoungTableau lam)
    (hu₁ : TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h₁ hr₁))
    (hu₂ :
      TableauMaxAt (S05_Lem5_13_deleteFirstMaxAsTableau h₁ hr₁ T hu₁)
        (deletedCornerCellOfOneBoxChildRow h₂ hr₂))
    (a : Fin n) :
    YoungCell.row
      (cellOfEntry
        (S05_Lem5_13_deleteSecondMaxAsTableau h₁ hr₁ h₂ hr₂ T hu₁ hu₂) a)
      =
    YoungCell.row
      (cellOfEntry
        (S05_Lem5_13_deleteFirstMaxAsTableau h₁ hr₁ T hu₁) (Fin.castSucc a)) := by
  exact S05_oneBoxIntertwining_deleteMax_cellOfEntry_row
    h₂ hr₂ (deletedCornerCellOfOneBoxChildRow h₂ hr₂)
    (deletedCornerCell_row h₂ hr₂) (deletedCornerCell_col h₂ hr₂)
    (S05_Lem5_13_deleteFirstMaxAsTableau h₁ hr₁ T hu₁) hu₂ a

/-- Lemma 5.4 basis-level component: the second deletion preserves columns
relative to the first-deleted tableau. -/
theorem S05_Lem5_13_second_deletion_cellOfEntry_col
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)} {nu : YoungDiagram n}
    (h₁ : IsOneBoxChild lam mu) {r₁ : Nat}
    (hr₁ :
      youngRow lam r₁ = youngRow mu r₁ + 1 ∧
      forall t : Nat, t ≠ r₁ -> youngRow lam t = youngRow mu t)
    (h₂ : IsOneBoxChild mu nu) {r₂ : Nat}
    (hr₂ :
      youngRow mu r₂ = youngRow nu r₂ + 1 ∧
      forall t : Nat, t ≠ r₂ -> youngRow mu t = youngRow nu t)
    (T : StandardYoungTableau lam)
    (hu₁ : TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h₁ hr₁))
    (hu₂ :
      TableauMaxAt (S05_Lem5_13_deleteFirstMaxAsTableau h₁ hr₁ T hu₁)
        (deletedCornerCellOfOneBoxChildRow h₂ hr₂))
    (a : Fin n) :
    YoungCell.col
      (cellOfEntry
        (S05_Lem5_13_deleteSecondMaxAsTableau h₁ hr₁ h₂ hr₂ T hu₁ hu₂) a)
      =
    YoungCell.col
      (cellOfEntry
        (S05_Lem5_13_deleteFirstMaxAsTableau h₁ hr₁ T hu₁) (Fin.castSucc a)) := by
  exact S05_oneBoxIntertwining_deleteMax_cellOfEntry_col
    h₂ hr₂ (deletedCornerCellOfOneBoxChildRow h₂ hr₂)
    (deletedCornerCell_row h₂ hr₂) (deletedCornerCell_col h₂ hr₂)
    (S05_Lem5_13_deleteFirstMaxAsTableau h₁ hr₁ T hu₁) hu₂ a

/-- Lemma 5.4 basis-level component: after two successive one-box deletions,
the content sequence is the original content sequence with the two largest
entries removed. -/
theorem S05_Lem5_13_iterated_deletion_tableauContentSequence
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)} {nu : YoungDiagram n}
    (h₁ : IsOneBoxChild lam mu) {r₁ : Nat}
    (hr₁ :
      youngRow lam r₁ = youngRow mu r₁ + 1 ∧
      forall t : Nat, t ≠ r₁ -> youngRow lam t = youngRow mu t)
    (h₂ : IsOneBoxChild mu nu) {r₂ : Nat}
    (hr₂ :
      youngRow mu r₂ = youngRow nu r₂ + 1 ∧
      forall t : Nat, t ≠ r₂ -> youngRow mu t = youngRow nu t)
    (T : StandardYoungTableau lam)
    (hu₁ : TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h₁ hr₁))
    (hu₂ :
      TableauMaxAt (S05_Lem5_13_deleteFirstMaxAsTableau h₁ hr₁ T hu₁)
        (deletedCornerCellOfOneBoxChildRow h₂ hr₂))
    (a : Fin n) :
    tableauContentSequence
        (S05_Lem5_13_deleteSecondMaxAsTableau h₁ hr₁ h₂ hr₂ T hu₁ hu₂) a
      =
    tableauContentSequence T (Fin.castSucc (Fin.castSucc a)) := by
  calc
    tableauContentSequence
        (S05_Lem5_13_deleteSecondMaxAsTableau h₁ hr₁ h₂ hr₂ T hu₁ hu₂) a
        =
      tableauContentSequence
        (S05_Lem5_13_deleteFirstMaxAsTableau h₁ hr₁ T hu₁) (Fin.castSucc a) := by
        exact S05_Lem5_13_second_deletion_tableauContentSequence
          h₁ hr₁ h₂ hr₂ T hu₁ hu₂ a
    _ = tableauContentSequence T (Fin.castSucc (Fin.castSucc a)) := by
        exact S05_Lem5_13_first_deletion_tableauContentSequence
          h₁ hr₁ T hu₁ (Fin.castSucc a)

/-- Lemma 5.4 basis-level component: after two successive one-box deletions,
each remaining entry has the row it had in the original tableau. -/
theorem S05_Lem5_13_iterated_deletion_cellOfEntry_row
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)} {nu : YoungDiagram n}
    (h₁ : IsOneBoxChild lam mu) {r₁ : Nat}
    (hr₁ :
      youngRow lam r₁ = youngRow mu r₁ + 1 ∧
      forall t : Nat, t ≠ r₁ -> youngRow lam t = youngRow mu t)
    (h₂ : IsOneBoxChild mu nu) {r₂ : Nat}
    (hr₂ :
      youngRow mu r₂ = youngRow nu r₂ + 1 ∧
      forall t : Nat, t ≠ r₂ -> youngRow mu t = youngRow nu t)
    (T : StandardYoungTableau lam)
    (hu₁ : TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h₁ hr₁))
    (hu₂ :
      TableauMaxAt (S05_Lem5_13_deleteFirstMaxAsTableau h₁ hr₁ T hu₁)
        (deletedCornerCellOfOneBoxChildRow h₂ hr₂))
    (a : Fin n) :
    YoungCell.row
      (cellOfEntry
        (S05_Lem5_13_deleteSecondMaxAsTableau h₁ hr₁ h₂ hr₂ T hu₁ hu₂) a)
      =
    YoungCell.row (cellOfEntry T (Fin.castSucc (Fin.castSucc a))) := by
  calc
    YoungCell.row
      (cellOfEntry
        (S05_Lem5_13_deleteSecondMaxAsTableau h₁ hr₁ h₂ hr₂ T hu₁ hu₂) a)
        =
      YoungCell.row
        (cellOfEntry
          (S05_Lem5_13_deleteFirstMaxAsTableau h₁ hr₁ T hu₁) (Fin.castSucc a)) := by
        exact S05_Lem5_13_second_deletion_cellOfEntry_row
          h₁ hr₁ h₂ hr₂ T hu₁ hu₂ a
    _ = YoungCell.row (cellOfEntry T (Fin.castSucc (Fin.castSucc a))) := by
        exact S05_Lem5_13_first_deletion_cellOfEntry_row
          h₁ hr₁ T hu₁ (Fin.castSucc a)

/-- Lemma 5.4 basis-level component: after two successive one-box deletions,
each remaining entry has the column it had in the original tableau. -/
theorem S05_Lem5_13_iterated_deletion_cellOfEntry_col
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)} {nu : YoungDiagram n}
    (h₁ : IsOneBoxChild lam mu) {r₁ : Nat}
    (hr₁ :
      youngRow lam r₁ = youngRow mu r₁ + 1 ∧
      forall t : Nat, t ≠ r₁ -> youngRow lam t = youngRow mu t)
    (h₂ : IsOneBoxChild mu nu) {r₂ : Nat}
    (hr₂ :
      youngRow mu r₂ = youngRow nu r₂ + 1 ∧
      forall t : Nat, t ≠ r₂ -> youngRow mu t = youngRow nu t)
    (T : StandardYoungTableau lam)
    (hu₁ : TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h₁ hr₁))
    (hu₂ :
      TableauMaxAt (S05_Lem5_13_deleteFirstMaxAsTableau h₁ hr₁ T hu₁)
        (deletedCornerCellOfOneBoxChildRow h₂ hr₂))
    (a : Fin n) :
    YoungCell.col
      (cellOfEntry
        (S05_Lem5_13_deleteSecondMaxAsTableau h₁ hr₁ h₂ hr₂ T hu₁ hu₂) a)
      =
    YoungCell.col (cellOfEntry T (Fin.castSucc (Fin.castSucc a))) := by
  calc
    YoungCell.col
      (cellOfEntry
        (S05_Lem5_13_deleteSecondMaxAsTableau h₁ hr₁ h₂ hr₂ T hu₁ hu₂) a)
        =
      YoungCell.col
        (cellOfEntry
          (S05_Lem5_13_deleteFirstMaxAsTableau h₁ hr₁ T hu₁) (Fin.castSucc a)) := by
        exact S05_Lem5_13_second_deletion_cellOfEntry_col
          h₁ hr₁ h₂ hr₂ T hu₁ hu₂ a
    _ = YoungCell.col (cellOfEntry T (Fin.castSucc (Fin.castSucc a))) := by
        exact S05_Lem5_13_first_deletion_cellOfEntry_col
          h₁ hr₁ T hu₁ (Fin.castSucc a)

/-- Lemma 5.4 set-level branching statement: fixing the two deleted removable
rows gives a bijection between parent tableaux following that two-step deletion
pattern and tableaux of the resulting child diagram. -/
noncomputable def S05_Lem5_13_twoStepDeletionTableauxEquivChildTableaux
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam) :
    TwoStepDeletionTableaux lam p ≃
      StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p) :=
  twoStepDeletionTableauxEquivChildTableaux lam p

/-- Extend a child tableau by placing the two largest entries according to a
fixed ordered two-step removal. -/
noncomputable def S05_Lem5_13_twoBoxExtensionTableau
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p)) :
    StandardYoungTableau lam :=
  ((S05_Lem5_13_twoStepDeletionTableauxEquivChildTableaux lam p).symm U).1.1

/-- The inverse of the fixed two-step deletion equivalence is the composite of
the two explicit one-box maximum-entry insertions. -/
theorem S05_Lem5_13_twoBoxExtensionTableau_eq_insertMax_twice
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p)) :
    S05_Lem5_13_twoBoxExtensionTableau lam p U =
      S05_oneBoxDeletion_insertMaxAsStandardYoungTableauOfOneBoxChildRow
        (twoStepFirstChild_isOneBoxChild lam p)
        (twoStepFirstChild_row_form lam p)
        (S05_oneBoxDeletion_insertMaxAsStandardYoungTableauOfOneBoxChildRow
          (twoStepSecondChild_isOneBoxChild lam p)
          (twoStepSecondChild_row_form lam p) U) := by
  rfl

/-- Two-box extension preserves the same-row test for every adjacent pair that
belongs to the child tableau. -/
theorem S05_Lem5_13_twoBoxExtensionTableau_earlier_sameRow_iff
    {n : Nat} (lam : YoungDiagram (((n + 1) + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p))
    (a : Fin n) :
    adjacentSameRow (S05_Lem5_13_twoBoxExtensionTableau lam p U)
        (Fin.castSucc (Fin.castSucc a)) ↔
      adjacentSameRow U a := by
  rw [S05_Lem5_13_twoBoxExtensionTableau_eq_insertMax_twice]
  rw [S05_oneBoxIntertwining_insertMax_adjacentSameRow_iff,
    S05_oneBoxIntertwining_insertMax_adjacentSameRow_iff]

/-- Two-box extension preserves the same-column test for every adjacent pair
that belongs to the child tableau. -/
theorem S05_Lem5_13_twoBoxExtensionTableau_earlier_sameCol_iff
    {n : Nat} (lam : YoungDiagram (((n + 1) + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p))
    (a : Fin n) :
    adjacentSameCol (S05_Lem5_13_twoBoxExtensionTableau lam p U)
        (Fin.castSucc (Fin.castSucc a)) ↔
      adjacentSameCol U a := by
  rw [S05_Lem5_13_twoBoxExtensionTableau_eq_insertMax_twice]
  rw [S05_oneBoxIntertwining_insertMax_adjacentSameCol_iff,
    S05_oneBoxIntertwining_insertMax_adjacentSameCol_iff]

/-- Two-box extension preserves the diagonal Young coefficient for every
adjacent pair that belongs to the child tableau. -/
theorem S05_Lem5_13_twoBoxExtensionTableau_earlier_diagCoeff
    {n : Nat} (lam : YoungDiagram (((n + 1) + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p))
    (a : Fin n) :
    youngAdjacentDiagCoeff (S05_Lem5_13_twoBoxExtensionTableau lam p U)
        (Fin.castSucc (Fin.castSucc a)) =
      youngAdjacentDiagCoeff U a := by
  rw [S05_Lem5_13_twoBoxExtensionTableau_eq_insertMax_twice]
  calc
    _ = youngAdjacentDiagCoeff
        (S05_oneBoxDeletion_insertMaxAsStandardYoungTableauOfOneBoxChildRow
          (twoStepSecondChild_isOneBoxChild lam p)
          (twoStepSecondChild_row_form lam p) U)
        (Fin.castSucc a) :=
      (S05_oneBoxIntertwining_insertMax_youngAdjacentDiagCoeff
        (twoStepFirstChild_isOneBoxChild lam p)
        (twoStepFirstChild_row_form lam p) _ (Fin.castSucc a)).symm
    _ = youngAdjacentDiagCoeff U a :=
      (S05_oneBoxIntertwining_insertMax_youngAdjacentDiagCoeff
        (twoStepSecondChild_isOneBoxChild lam p)
        (twoStepSecondChild_row_form lam p) U a).symm

/-- Two-box extension preserves the off-diagonal Young coefficient for every
adjacent pair that belongs to the child tableau. -/
theorem S05_Lem5_13_twoBoxExtensionTableau_earlier_offCoeff
    {n : Nat} (lam : YoungDiagram (((n + 1) + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p))
    (a : Fin n) :
    youngAdjacentOffCoeff (S05_Lem5_13_twoBoxExtensionTableau lam p U)
        (Fin.castSucc (Fin.castSucc a)) =
      youngAdjacentOffCoeff U a := by
  rw [S05_Lem5_13_twoBoxExtensionTableau_eq_insertMax_twice]
  calc
    _ = youngAdjacentOffCoeff
        (S05_oneBoxDeletion_insertMaxAsStandardYoungTableauOfOneBoxChildRow
          (twoStepSecondChild_isOneBoxChild lam p)
          (twoStepSecondChild_row_form lam p) U)
        (Fin.castSucc a) :=
      (S05_oneBoxIntertwining_insertMax_youngAdjacentOffCoeff
        (twoStepFirstChild_isOneBoxChild lam p)
        (twoStepFirstChild_row_form lam p) _ (Fin.castSucc a)).symm
    _ = youngAdjacentOffCoeff U a :=
      (S05_oneBoxIntertwining_insertMax_youngAdjacentOffCoeff
        (twoStepSecondChild_isOneBoxChild lam p)
        (twoStepSecondChild_row_form lam p) U a).symm

/-- Swapping an adjacent pair belonging to the child commutes with the explicit
two-box extension. -/
theorem S05_Lem5_13_twoBoxExtensionTableau_earlier_swap
    {n : Nat} (lam : YoungDiagram (((n + 1) + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p))
    (a : Fin n)
    (hrow : ¬ adjacentSameRow U a) (hcol : ¬ adjacentSameCol U a) :
    S05_Lem5_13_twoBoxExtensionTableau lam p
        (adjacentSwapTableau U a hrow hcol) =
      adjacentSwapTableau (S05_Lem5_13_twoBoxExtensionTableau lam p U)
        (Fin.castSucc (Fin.castSucc a))
        (by
          intro hp
          exact hrow
            ((S05_Lem5_13_twoBoxExtensionTableau_earlier_sameRow_iff
              lam p U a).1 hp))
        (by
          intro hp
          exact hcol
            ((S05_Lem5_13_twoBoxExtensionTableau_earlier_sameCol_iff
              lam p U a).1 hp)) := by
  let U1 := S05_oneBoxDeletion_insertMaxAsStandardYoungTableauOfOneBoxChildRow
    (twoStepSecondChild_isOneBoxChild lam p)
    (twoStepSecondChild_row_form lam p) U
  have hrow1 : ¬ adjacentSameRow U1 (Fin.castSucc a) := by
    intro hp
    exact hrow ((S05_oneBoxIntertwining_insertMax_adjacentSameRow_iff
      (twoStepSecondChild_isOneBoxChild lam p)
      (twoStepSecondChild_row_form lam p) U a).1 hp)
  have hcol1 : ¬ adjacentSameCol U1 (Fin.castSucc a) := by
    intro hp
    exact hcol ((S05_oneBoxIntertwining_insertMax_adjacentSameCol_iff
      (twoStepSecondChild_isOneBoxChild lam p)
      (twoStepSecondChild_row_form lam p) U a).1 hp)
  have hsecond := S05_oneBoxIntertwining_insertMax_adjacentSwapTableau
    (twoStepSecondChild_isOneBoxChild lam p)
    (twoStepSecondChild_row_form lam p) U a hrow hcol
  have hfirst := S05_oneBoxIntertwining_insertMax_adjacentSwapTableau
    (twoStepFirstChild_isOneBoxChild lam p)
    (twoStepFirstChild_row_form lam p) U1 (Fin.castSucc a) hrow1 hcol1
  calc
    S05_Lem5_13_twoBoxExtensionTableau lam p
        (adjacentSwapTableau U a hrow hcol) =
      S05_oneBoxDeletion_insertMaxAsStandardYoungTableauOfOneBoxChildRow
        (twoStepFirstChild_isOneBoxChild lam p)
        (twoStepFirstChild_row_form lam p)
        (S05_oneBoxDeletion_insertMaxAsStandardYoungTableauOfOneBoxChildRow
          (twoStepSecondChild_isOneBoxChild lam p)
          (twoStepSecondChild_row_form lam p)
          (adjacentSwapTableau U a hrow hcol)) :=
      S05_Lem5_13_twoBoxExtensionTableau_eq_insertMax_twice lam p _
    _ = S05_oneBoxDeletion_insertMaxAsStandardYoungTableauOfOneBoxChildRow
        (twoStepFirstChild_isOneBoxChild lam p)
        (twoStepFirstChild_row_form lam p)
        (adjacentSwapTableau U1 (Fin.castSucc a) hrow1 hcol1) := by
      exact congrArg
        (S05_oneBoxDeletion_insertMaxAsStandardYoungTableauOfOneBoxChildRow
          (twoStepFirstChild_isOneBoxChild lam p)
          (twoStepFirstChild_row_form lam p)) hsecond
    _ = adjacentSwapTableau
        (S05_oneBoxDeletion_insertMaxAsStandardYoungTableauOfOneBoxChildRow
          (twoStepFirstChild_isOneBoxChild lam p)
          (twoStepFirstChild_row_form lam p) U1)
        (Fin.castSucc (Fin.castSucc a)) _ _ := hfirst
    _ = adjacentSwapTableau (S05_Lem5_13_twoBoxExtensionTableau lam p U)
        (Fin.castSucc (Fin.castSucc a)) _ _ := by
      have hbase :
          S05_oneBoxDeletion_insertMaxAsStandardYoungTableauOfOneBoxChildRow
              (twoStepFirstChild_isOneBoxChild lam p)
              (twoStepFirstChild_row_form lam p) U1 =
            S05_Lem5_13_twoBoxExtensionTableau lam p U := by
        exact (S05_Lem5_13_twoBoxExtensionTableau_eq_insertMax_twice
          lam p U).symm
      cases hbase
      rfl

/-- Distinct child tableaux have distinct extensions in a fixed two-step
deletion fiber. -/
theorem S05_Lem5_13_twoBoxExtensionTableau_injective
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam) :
    Function.Injective (S05_Lem5_13_twoBoxExtensionTableau lam p) := by
  intro U V hUV
  let e := S05_Lem5_13_twoStepDeletionTableauxEquivChildTableaux lam p
  apply e.symm.injective
  apply Subtype.ext
  apply Subtype.ext
  exact hUV

/-- The largest entry of a two-box extension occupies the first deleted
corner. -/
theorem S05_Lem5_13_twoBoxExtensionTableau_maxAt_firstCorner
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p)) :
    TableauMaxAt (S05_Lem5_13_twoBoxExtensionTableau lam p U)
      (firstDeletedCornerOfTwoStep lam p) := by
  exact
    ((S05_Lem5_13_twoStepDeletionTableauxEquivChildTableaux lam p).symm U).1.2

/-- After deleting the largest entry of a two-box extension, the next largest
entry occupies the second deleted corner. -/
theorem S05_Lem5_13_twoBoxExtensionTableau_nextMaxAt_secondCorner
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p)) :
    TableauMaxAt
      (twoStepFirstDeletionEquiv lam p
        ((S05_Lem5_13_twoStepDeletionTableauxEquivChildTableaux lam p).symm U).1)
      (secondDeletedCornerOfTwoStepInChild lam p) := by
  exact
    ((S05_Lem5_13_twoStepDeletionTableauxEquivChildTableaux lam p).symm U).2

/-- In a two-box extension, the higher of the final adjacent labels occupies
the first deleted corner. -/
theorem S05_Lem5_13_twoBoxExtensionTableau_final_hiCell
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p)) :
    adjacentHiCell (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n) =
      firstDeletedCornerOfTwoStep lam p := by
  unfold adjacentHiCell
  apply cellOfEntry_eq_of_entry
  have hmax :=
    S05_Lem5_13_twoBoxExtensionTableau_maxAt_firstCorner lam p U
  unfold TableauMaxAt at hmax
  rw [hmax]
  apply Fin.ext
  rfl

/-- In a two-box extension, the lower of the final adjacent labels occupies
the second deleted corner, viewed in the parent diagram. -/
theorem S05_Lem5_13_twoBoxExtensionTableau_final_loCell
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p)) :
    adjacentLoCell (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n) =
      secondDeletedCornerOfTwoStepInParent lam p := by
  let e := S05_Lem5_13_twoStepDeletionTableauxEquivChildTableaux lam p
  let X := e.symm U
  let T := S05_Lem5_13_twoBoxExtensionTableau lam p U
  have hsecond :
      cellOfEntry (twoStepFirstDeletionEquiv lam p X.1) (Fin.last n) =
        secondDeletedCornerOfTwoStepInChild lam p := by
    apply cellOfEntry_eq_of_entry
    simpa [TableauMaxAt] using X.2
  have hmap := S05_Lem5_13_first_deletion_childCellToParent_cellOfEntry
    (twoStepFirstChild_isOneBoxChild lam p)
    (twoStepFirstChild_row_form lam p)
    T X.1.2 (Fin.last n)
  change cellOfEntry T (Fin.castSucc (Fin.last n)) =
    secondDeletedCornerOfTwoStepInParent lam p
  rw [secondDeletedCornerOfTwoStepInParent]
  rw [← hsecond]
  exact hmap.symm

/-- The lower final label lies in the second deleted row. -/
theorem S05_Lem5_13_twoBoxExtensionTableau_final_loCell_row
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p)) :
    YoungCell.row
        (adjacentLoCell (S05_Lem5_13_twoBoxExtensionTableau lam p U)
          (Fin.last n)) =
      p.second.1 := by
  rw [S05_Lem5_13_twoBoxExtensionTableau_final_loCell]
  exact secondDeletedCornerOfTwoStepInParent_row lam p

/-- The higher final label lies in the first deleted row. -/
theorem S05_Lem5_13_twoBoxExtensionTableau_final_hiCell_row
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p)) :
    YoungCell.row
        (adjacentHiCell (S05_Lem5_13_twoBoxExtensionTableau lam p U)
          (Fin.last n)) =
      p.first.1 := by
  rw [S05_Lem5_13_twoBoxExtensionTableau_final_hiCell]
  exact firstDeletedCornerOfTwoStep_row lam p

/-- The final adjacent labels of an extension share a row exactly when the two
deletions use the same row. -/
theorem S05_Lem5_13_twoBoxExtensionTableau_final_sameRow_iff
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p)) :
    adjacentSameRow (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n) ↔
      p.second.1 = p.first.1 := by
  unfold adjacentSameRow
  rw [S05_Lem5_13_twoBoxExtensionTableau_final_loCell_row,
    S05_Lem5_13_twoBoxExtensionTableau_final_hiCell_row]

/-- The column of the lower final label is fixed by the two-step removal. -/
theorem S05_Lem5_13_twoBoxExtensionTableau_final_loCell_col
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p)) :
    YoungCell.col
        (adjacentLoCell (S05_Lem5_13_twoBoxExtensionTableau lam p U)
          (Fin.last n)) =
      youngRow (deleteTwoRemovableRowsDiagram lam p) p.second.1 := by
  rw [S05_Lem5_13_twoBoxExtensionTableau_final_loCell]
  exact secondDeletedCornerOfTwoStepInParent_col lam p

/-- The column of the higher final label is fixed by the two-step removal. -/
theorem S05_Lem5_13_twoBoxExtensionTableau_final_hiCell_col
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p)) :
    YoungCell.col
        (adjacentHiCell (S05_Lem5_13_twoBoxExtensionTableau lam p U)
          (Fin.last n)) =
      youngRow (twoStepFirstChild lam p) p.first.1 := by
  rw [S05_Lem5_13_twoBoxExtensionTableau_final_hiCell]
  exact firstDeletedCornerOfTwoStep_col lam p

/-- Whether the final adjacent labels share a column depends only on the
ordered two-step removal, not on the child tableau. -/
theorem S05_Lem5_13_twoBoxExtensionTableau_final_sameCol_iff
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p)) :
    adjacentSameCol (S05_Lem5_13_twoBoxExtensionTableau lam p U) (Fin.last n) ↔
      youngRow (deleteTwoRemovableRowsDiagram lam p) p.second.1 =
        youngRow (twoStepFirstChild lam p) p.first.1 := by
  unfold adjacentSameCol
  rw [S05_Lem5_13_twoBoxExtensionTableau_final_loCell_col,
    S05_Lem5_13_twoBoxExtensionTableau_final_hiCell_col]

/-- The axial distance of the final two labels depends only on the two removed
boxes, not on the child tableau. -/
theorem S05_Lem5_13_twoBoxExtensionTableau_final_axialDistance_eq
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (U V : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p)) :
    adjacentAxialDistance (S05_Lem5_13_twoBoxExtensionTableau lam p U)
        (Fin.last n) =
      adjacentAxialDistance (S05_Lem5_13_twoBoxExtensionTableau lam p V)
        (Fin.last n) := by
  unfold adjacentAxialDistance entryContent
  change
    YoungCell.content
          (adjacentHiCell (S05_Lem5_13_twoBoxExtensionTableau lam p U)
            (Fin.last n)) -
        YoungCell.content
          (adjacentLoCell (S05_Lem5_13_twoBoxExtensionTableau lam p U)
            (Fin.last n)) =
      YoungCell.content
          (adjacentHiCell (S05_Lem5_13_twoBoxExtensionTableau lam p V)
            (Fin.last n)) -
        YoungCell.content
          (adjacentLoCell (S05_Lem5_13_twoBoxExtensionTableau lam p V)
            (Fin.last n))
  rw [S05_Lem5_13_twoBoxExtensionTableau_final_hiCell,
    S05_Lem5_13_twoBoxExtensionTableau_final_loCell,
    S05_Lem5_13_twoBoxExtensionTableau_final_hiCell,
    S05_Lem5_13_twoBoxExtensionTableau_final_loCell]

/-- The diagonal coefficient of the final Young block is constant across a
fixed two-step extension fiber. -/
theorem S05_Lem5_13_twoBoxExtensionTableau_final_diagCoeff_eq
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (U V : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p)) :
    youngAdjacentDiagCoeff (S05_Lem5_13_twoBoxExtensionTableau lam p U)
        (Fin.last n) =
      youngAdjacentDiagCoeff (S05_Lem5_13_twoBoxExtensionTableau lam p V)
        (Fin.last n) := by
  unfold youngAdjacentDiagCoeff
  rw [S05_Lem5_13_twoBoxExtensionTableau_final_axialDistance_eq lam p U V]

/-- The off-diagonal coefficient of the final Young block is constant across a
fixed two-step extension fiber. -/
theorem S05_Lem5_13_twoBoxExtensionTableau_final_offCoeff_eq
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (U V : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p)) :
    youngAdjacentOffCoeff (S05_Lem5_13_twoBoxExtensionTableau lam p U)
        (Fin.last n) =
      youngAdjacentOffCoeff (S05_Lem5_13_twoBoxExtensionTableau lam p V)
        (Fin.last n) := by
  unfold youngAdjacentOffCoeff
  rw [S05_Lem5_13_twoBoxExtensionTableau_final_diagCoeff_eq lam p U V]

/-- Restricting a two-box extension to an earlier entry preserves the row of
that entry in the child tableau. -/
theorem S05_Lem5_13_twoBoxExtensionTableau_child_cellOfEntry_row
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p))
    (a : Fin n) :
    YoungCell.row (cellOfEntry U a) =
      YoungCell.row
        (cellOfEntry (S05_Lem5_13_twoBoxExtensionTableau lam p U)
          (Fin.castSucc (Fin.castSucc a))) := by
  let e := S05_Lem5_13_twoStepDeletionTableauxEquivChildTableaux lam p
  let X := e.symm U
  let T := S05_Lem5_13_twoBoxExtensionTableau lam p U
  have hiter := S05_Lem5_13_iterated_deletion_cellOfEntry_row
    (twoStepFirstChild_isOneBoxChild lam p)
    (twoStepFirstChild_row_form lam p)
    (twoStepSecondChild_isOneBoxChild lam p)
    (twoStepSecondChild_row_form lam p)
    T X.1.2 X.2 a
  change
    YoungCell.row (cellOfEntry (e X) a) =
      YoungCell.row (cellOfEntry T (Fin.castSucc (Fin.castSucc a))) at hiter
  rw [e.apply_symm_apply U] at hiter
  exact hiter

/-- Restricting a two-box extension to an earlier entry preserves the column
of that entry in the child tableau. -/
theorem S05_Lem5_13_twoBoxExtensionTableau_child_cellOfEntry_col
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p))
    (a : Fin n) :
    YoungCell.col (cellOfEntry U a) =
      YoungCell.col
        (cellOfEntry (S05_Lem5_13_twoBoxExtensionTableau lam p U)
          (Fin.castSucc (Fin.castSucc a))) := by
  let e := S05_Lem5_13_twoStepDeletionTableauxEquivChildTableaux lam p
  let X := e.symm U
  let T := S05_Lem5_13_twoBoxExtensionTableau lam p U
  have hiter := S05_Lem5_13_iterated_deletion_cellOfEntry_col
    (twoStepFirstChild_isOneBoxChild lam p)
    (twoStepFirstChild_row_form lam p)
    (twoStepSecondChild_isOneBoxChild lam p)
    (twoStepSecondChild_row_form lam p)
    T X.1.2 X.2 a
  change
    YoungCell.col (cellOfEntry (e X) a) =
      YoungCell.col (cellOfEntry T (Fin.castSucc (Fin.castSucc a))) at hiter
  rw [e.apply_symm_apply U] at hiter
  exact hiter

/-- Lemma 5.4 cardinality form of the fixed two-step tableau branching
bijection. -/
theorem S05_Lem5_13_card_twoStepDeletionTableaux_eq_child
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam) :
    Fintype.card (TwoStepDeletionTableaux lam p) =
      Fintype.card
        (StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p)) := by
  exact card_twoStepDeletionTableaux_eq_child lam p

/-- Lemma 5.4 dimension form of the fixed two-step tableau branching
bijection. -/
theorem S05_Lem5_13_tableauDim_fixed_twoStepDeletion
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam) :
    ((Fintype.card (TwoStepDeletionTableaux lam p) : Nat) : ℝ) =
      tableauDim (deleteTwoRemovableRowsDiagram lam p) := by
  exact tableauDim_fixed_twoStepDeletion lam p

end DictatorshipTesting
