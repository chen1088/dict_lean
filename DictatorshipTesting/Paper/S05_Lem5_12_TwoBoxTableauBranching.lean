import DictatorshipTesting.Paper.S05_Def5_10_SignedTwoBoxRemovals
import DictatorshipTesting.Paper.Aux_TableauDimension
import DictatorshipTesting.Paper.S05_Lem5_15_OneBoxDeletionIsUnitary
import DictatorshipTesting.Paper.S05_Lem5_16_OneBoxDeletionIntertwinesEarlierSwaps

/-
Direct reverse imports:
- `DictatorshipTesting`
-/

/-!
Paper statement: Lemma 5.12 (`lem:two-box-tableau-branching`)
Title in paper: Two-box tableau branching.

Status: proven. Proved below as a concrete set-level tableau branching statement for a
fixed two-step deletion pattern, with content/row/column preservation wrappers.
No Specht-module branching theorem is asserted here.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.13 set-level component: perform the first one-box deletion in an
iterated two-box tableau deletion. -/
def S05_Lem5_12_deleteFirstMaxAsTableau
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

/-- Lemma 5.13 set-level component: the first deleted cell is a removable corner
of the parent tableau shape. -/
theorem S05_Lem5_12_first_deleted_cell_removable_corner
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

/-- Lemma 5.13 set-level component: after deleting the largest entry, the new
largest entry lies in a unique removable corner of the child shape. -/
theorem S05_Lem5_12_after_first_deletion_unique_second_corner
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (T : StandardYoungTableau lam)
    (hu : TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h hr)) :
    ∃! v : YoungCell mu,
      TableauMaxAt (S05_Lem5_12_deleteFirstMaxAsTableau h hr T hu) v ∧
        IsRemovableCornerBox mu (YoungCell.toNatPair v) := by
  exact existsUnique_removableCornerBox_tableauMaxAt
    (S05_Lem5_12_deleteFirstMaxAsTableau h hr T hu)

/-- Lemma 5.13 set-level component: any second maximum-entry cell after the first
deletion is a removable corner of the child shape. -/
theorem S05_Lem5_12_second_deleted_cell_removable_corner
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (T : StandardYoungTableau lam)
    (hu : TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h hr))
    {v : YoungCell mu}
    (hv : TableauMaxAt (S05_Lem5_12_deleteFirstMaxAsTableau h hr T hu) v) :
    IsRemovableCornerBox mu (YoungCell.toNatPair v) := by
  exact removableCornerBox_of_tableauMaxAt
    (S05_Lem5_12_deleteFirstMaxAsTableau h hr T hu) hv

/-- Lemma 5.13 basis-level component: the first deletion in the two-box
branching step preserves the content sequence on the remaining entries. -/
theorem S05_Lem5_12_first_deletion_tableauContentSequence
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (T : StandardYoungTableau lam)
    (hu : TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h hr))
    (a : Fin (n + 1)) :
    tableauContentSequence (S05_Lem5_12_deleteFirstMaxAsTableau h hr T hu) a =
      tableauContentSequence T (Fin.castSucc a) := by
  exact S05_Lem5_16_deleteMax_tableauContentSequence
    h hr (deletedCornerCellOfOneBoxChildRow h hr)
    (deletedCornerCell_row h hr) (deletedCornerCell_col h hr) T hu a

/-- Lemma 5.13 basis-level component: after the first deletion, the child cell
containing a remaining entry maps back to the original parent cell. -/
theorem S05_Lem5_12_first_deletion_childCellToParent_cellOfEntry
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
      (cellOfEntry (S05_Lem5_12_deleteFirstMaxAsTableau h hr T hu) a)
      =
    cellOfEntry T (Fin.castSucc a) := by
  exact S05_Lem5_16_childCellToParent_cellOfEntry_deleteMax
    h hr (deletedCornerCellOfOneBoxChildRow h hr)
    (deletedCornerCell_row h hr) (deletedCornerCell_col h hr) T hu a

/-- Lemma 5.13 basis-level component: the first deletion preserves the row of
each remaining entry. -/
theorem S05_Lem5_12_first_deletion_cellOfEntry_row
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
      (cellOfEntry (S05_Lem5_12_deleteFirstMaxAsTableau h hr T hu) a)
      =
    YoungCell.row (cellOfEntry T (Fin.castSucc a)) := by
  exact S05_Lem5_16_deleteMax_cellOfEntry_row
    h hr (deletedCornerCellOfOneBoxChildRow h hr)
    (deletedCornerCell_row h hr) (deletedCornerCell_col h hr) T hu a

/-- Lemma 5.13 basis-level component: the first deletion preserves the column of
each remaining entry. -/
theorem S05_Lem5_12_first_deletion_cellOfEntry_col
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
      (cellOfEntry (S05_Lem5_12_deleteFirstMaxAsTableau h hr T hu) a)
      =
    YoungCell.col (cellOfEntry T (Fin.castSucc a)) := by
  exact S05_Lem5_16_deleteMax_cellOfEntry_col
    h hr (deletedCornerCellOfOneBoxChildRow h hr)
    (deletedCornerCell_row h hr) (deletedCornerCell_col h hr) T hu a

/-- Lemma 5.13 set-level component: perform the second one-box deletion after
the first one in an iterated two-box tableau deletion. -/
def S05_Lem5_12_deleteSecondMaxAsTableau
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
      TableauMaxAt (S05_Lem5_12_deleteFirstMaxAsTableau h₁ hr₁ T hu₁)
        (deletedCornerCellOfOneBoxChildRow h₂ hr₂)) :
    StandardYoungTableau nu :=
  deleteMaxAsStandardYoungTableauOfOneBoxChildRow
    h₂ hr₂
    (deletedCornerCellOfOneBoxChildRow h₂ hr₂)
    (deletedCornerCell_row h₂ hr₂)
    (deletedCornerCell_col h₂ hr₂)
    (S05_Lem5_12_deleteFirstMaxAsTableau h₁ hr₁ T hu₁) hu₂

/-- Lemma 5.13 basis-level component: the second deletion preserves the content
sequence on entries remaining after that deletion. -/
theorem S05_Lem5_12_second_deletion_tableauContentSequence
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
      TableauMaxAt (S05_Lem5_12_deleteFirstMaxAsTableau h₁ hr₁ T hu₁)
        (deletedCornerCellOfOneBoxChildRow h₂ hr₂))
    (a : Fin n) :
    tableauContentSequence
        (S05_Lem5_12_deleteSecondMaxAsTableau h₁ hr₁ h₂ hr₂ T hu₁ hu₂) a
      =
    tableauContentSequence
        (S05_Lem5_12_deleteFirstMaxAsTableau h₁ hr₁ T hu₁) (Fin.castSucc a) := by
  exact S05_Lem5_16_deleteMax_tableauContentSequence
    h₂ hr₂ (deletedCornerCellOfOneBoxChildRow h₂ hr₂)
    (deletedCornerCell_row h₂ hr₂) (deletedCornerCell_col h₂ hr₂)
    (S05_Lem5_12_deleteFirstMaxAsTableau h₁ hr₁ T hu₁) hu₂ a

/-- Lemma 5.13 basis-level component: after the second deletion, the child cell
containing a remaining entry maps back to its cell after the first deletion. -/
theorem S05_Lem5_12_second_deletion_childCellToParent_cellOfEntry
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
      TableauMaxAt (S05_Lem5_12_deleteFirstMaxAsTableau h₁ hr₁ T hu₁)
        (deletedCornerCellOfOneBoxChildRow h₂ hr₂))
    (a : Fin n) :
    childCellToParentCellOfOneBoxChildRow h₂ hr₂
      (cellOfEntry
        (S05_Lem5_12_deleteSecondMaxAsTableau h₁ hr₁ h₂ hr₂ T hu₁ hu₂) a)
      =
    cellOfEntry
      (S05_Lem5_12_deleteFirstMaxAsTableau h₁ hr₁ T hu₁) (Fin.castSucc a) := by
  exact S05_Lem5_16_childCellToParent_cellOfEntry_deleteMax
    h₂ hr₂ (deletedCornerCellOfOneBoxChildRow h₂ hr₂)
    (deletedCornerCell_row h₂ hr₂) (deletedCornerCell_col h₂ hr₂)
    (S05_Lem5_12_deleteFirstMaxAsTableau h₁ hr₁ T hu₁) hu₂ a

/-- Lemma 5.13 basis-level component: the second deletion preserves rows relative
to the first-deleted tableau. -/
theorem S05_Lem5_12_second_deletion_cellOfEntry_row
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
      TableauMaxAt (S05_Lem5_12_deleteFirstMaxAsTableau h₁ hr₁ T hu₁)
        (deletedCornerCellOfOneBoxChildRow h₂ hr₂))
    (a : Fin n) :
    YoungCell.row
      (cellOfEntry
        (S05_Lem5_12_deleteSecondMaxAsTableau h₁ hr₁ h₂ hr₂ T hu₁ hu₂) a)
      =
    YoungCell.row
      (cellOfEntry
        (S05_Lem5_12_deleteFirstMaxAsTableau h₁ hr₁ T hu₁) (Fin.castSucc a)) := by
  exact S05_Lem5_16_deleteMax_cellOfEntry_row
    h₂ hr₂ (deletedCornerCellOfOneBoxChildRow h₂ hr₂)
    (deletedCornerCell_row h₂ hr₂) (deletedCornerCell_col h₂ hr₂)
    (S05_Lem5_12_deleteFirstMaxAsTableau h₁ hr₁ T hu₁) hu₂ a

/-- Lemma 5.13 basis-level component: the second deletion preserves columns
relative to the first-deleted tableau. -/
theorem S05_Lem5_12_second_deletion_cellOfEntry_col
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
      TableauMaxAt (S05_Lem5_12_deleteFirstMaxAsTableau h₁ hr₁ T hu₁)
        (deletedCornerCellOfOneBoxChildRow h₂ hr₂))
    (a : Fin n) :
    YoungCell.col
      (cellOfEntry
        (S05_Lem5_12_deleteSecondMaxAsTableau h₁ hr₁ h₂ hr₂ T hu₁ hu₂) a)
      =
    YoungCell.col
      (cellOfEntry
        (S05_Lem5_12_deleteFirstMaxAsTableau h₁ hr₁ T hu₁) (Fin.castSucc a)) := by
  exact S05_Lem5_16_deleteMax_cellOfEntry_col
    h₂ hr₂ (deletedCornerCellOfOneBoxChildRow h₂ hr₂)
    (deletedCornerCell_row h₂ hr₂) (deletedCornerCell_col h₂ hr₂)
    (S05_Lem5_12_deleteFirstMaxAsTableau h₁ hr₁ T hu₁) hu₂ a

/-- Lemma 5.13 basis-level component: after two successive one-box deletions,
the content sequence is the original content sequence with the two largest
entries removed. -/
theorem S05_Lem5_12_iterated_deletion_tableauContentSequence
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
      TableauMaxAt (S05_Lem5_12_deleteFirstMaxAsTableau h₁ hr₁ T hu₁)
        (deletedCornerCellOfOneBoxChildRow h₂ hr₂))
    (a : Fin n) :
    tableauContentSequence
        (S05_Lem5_12_deleteSecondMaxAsTableau h₁ hr₁ h₂ hr₂ T hu₁ hu₂) a
      =
    tableauContentSequence T (Fin.castSucc (Fin.castSucc a)) := by
  calc
    tableauContentSequence
        (S05_Lem5_12_deleteSecondMaxAsTableau h₁ hr₁ h₂ hr₂ T hu₁ hu₂) a
        =
      tableauContentSequence
        (S05_Lem5_12_deleteFirstMaxAsTableau h₁ hr₁ T hu₁) (Fin.castSucc a) := by
        exact S05_Lem5_12_second_deletion_tableauContentSequence
          h₁ hr₁ h₂ hr₂ T hu₁ hu₂ a
    _ = tableauContentSequence T (Fin.castSucc (Fin.castSucc a)) := by
        exact S05_Lem5_12_first_deletion_tableauContentSequence
          h₁ hr₁ T hu₁ (Fin.castSucc a)

/-- Lemma 5.13 basis-level component: after two successive one-box deletions,
each remaining entry has the row it had in the original tableau. -/
theorem S05_Lem5_12_iterated_deletion_cellOfEntry_row
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
      TableauMaxAt (S05_Lem5_12_deleteFirstMaxAsTableau h₁ hr₁ T hu₁)
        (deletedCornerCellOfOneBoxChildRow h₂ hr₂))
    (a : Fin n) :
    YoungCell.row
      (cellOfEntry
        (S05_Lem5_12_deleteSecondMaxAsTableau h₁ hr₁ h₂ hr₂ T hu₁ hu₂) a)
      =
    YoungCell.row (cellOfEntry T (Fin.castSucc (Fin.castSucc a))) := by
  calc
    YoungCell.row
      (cellOfEntry
        (S05_Lem5_12_deleteSecondMaxAsTableau h₁ hr₁ h₂ hr₂ T hu₁ hu₂) a)
        =
      YoungCell.row
        (cellOfEntry
          (S05_Lem5_12_deleteFirstMaxAsTableau h₁ hr₁ T hu₁) (Fin.castSucc a)) := by
        exact S05_Lem5_12_second_deletion_cellOfEntry_row
          h₁ hr₁ h₂ hr₂ T hu₁ hu₂ a
    _ = YoungCell.row (cellOfEntry T (Fin.castSucc (Fin.castSucc a))) := by
        exact S05_Lem5_12_first_deletion_cellOfEntry_row
          h₁ hr₁ T hu₁ (Fin.castSucc a)

/-- Lemma 5.13 basis-level component: after two successive one-box deletions,
each remaining entry has the column it had in the original tableau. -/
theorem S05_Lem5_12_iterated_deletion_cellOfEntry_col
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
      TableauMaxAt (S05_Lem5_12_deleteFirstMaxAsTableau h₁ hr₁ T hu₁)
        (deletedCornerCellOfOneBoxChildRow h₂ hr₂))
    (a : Fin n) :
    YoungCell.col
      (cellOfEntry
        (S05_Lem5_12_deleteSecondMaxAsTableau h₁ hr₁ h₂ hr₂ T hu₁ hu₂) a)
      =
    YoungCell.col (cellOfEntry T (Fin.castSucc (Fin.castSucc a))) := by
  calc
    YoungCell.col
      (cellOfEntry
        (S05_Lem5_12_deleteSecondMaxAsTableau h₁ hr₁ h₂ hr₂ T hu₁ hu₂) a)
        =
      YoungCell.col
        (cellOfEntry
          (S05_Lem5_12_deleteFirstMaxAsTableau h₁ hr₁ T hu₁) (Fin.castSucc a)) := by
        exact S05_Lem5_12_second_deletion_cellOfEntry_col
          h₁ hr₁ h₂ hr₂ T hu₁ hu₂ a
    _ = YoungCell.col (cellOfEntry T (Fin.castSucc (Fin.castSucc a))) := by
        exact S05_Lem5_12_first_deletion_cellOfEntry_col
          h₁ hr₁ T hu₁ (Fin.castSucc a)

/-- Lemma 5.12 set-level branching statement: fixing the two deleted removable
rows gives a bijection between parent tableaux following that two-step deletion
pattern and tableaux of the resulting child diagram. -/
noncomputable def S05_Lem5_12_twoStepDeletionTableauxEquivChildTableaux
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam) :
    TwoStepDeletionTableaux lam p ≃
      StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p) :=
  twoStepDeletionTableauxEquivChildTableaux lam p

/-- Lemma 5.12 cardinality form of the fixed two-step tableau branching
bijection. -/
theorem S05_Lem5_12_card_twoStepDeletionTableaux_eq_child
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam) :
    Fintype.card (TwoStepDeletionTableaux lam p) =
      Fintype.card
        (StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p)) := by
  exact card_twoStepDeletionTableaux_eq_child lam p

/-- Lemma 5.12 dimension form of the fixed two-step tableau branching
bijection. -/
theorem S05_Lem5_12_tableauDim_fixed_twoStepDeletion
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam) :
    ((Fintype.card (TwoStepDeletionTableaux lam p) : Nat) : ℝ) =
      tableauDim (deleteTwoRemovableRowsDiagram lam p) := by
  exact tableauDim_fixed_twoStepDeletion lam p

end DictatorshipTesting
