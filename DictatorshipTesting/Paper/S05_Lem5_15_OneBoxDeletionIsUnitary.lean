import DictatorshipTesting.Paper.Aux_YoungOrthogonal

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_12_TwoBoxTableauBranching`
- `DictatorshipTesting.Paper.S05_Lem5_16_OneBoxDeletionIntertwinesEarlierSwaps`
-/


/-!
Paper statement: Lemma 5.15 (`lem:one-box-deletion-unitary`)
Title in paper: One-box deletion is unitary.

Status: proven. Proved below for the concrete coordinate model: deletion gives a
set-level bijection on the deleted tableau basis, and the induced coordinate
map preserves the finite coordinate inner product.
-/

noncomputable section

namespace DictatorshipTesting

open scoped BigOperators

/-- Lemma 5.15 set-level component: deleting the maximum-entry cell gives a
bijection from the remaining cells to `Fin n`. -/
theorem S05_Lem5_15_deleteMaxEntry_bijective {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) {u : YoungCell lam}
    (hu : TableauMaxAt T u) :
    Function.Bijective (tableauDeleteMaxEntry T hu) := by
  exact tableauDeleteMaxEntry_bijective T hu

/-- Compatibility short name for the set-level deletion bijection. -/
theorem S05_oneBox_deleteMaxEntry_bijective {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) {u : YoungCell lam}
    (hu : TableauMaxAt T u) :
    Function.Bijective (tableauDeleteMaxEntry T hu) := by
  exact S05_Lem5_15_deleteMaxEntry_bijective T hu

/-- Lemma 5.15 set-level component: deleted entries remain row-strict. -/
theorem S05_Lem5_15_deleteMaxEntry_row_strict {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) {u : YoungCell lam}
    (hu : TableauMaxAt T u) :
    forall {a b : YoungCellExcept u},
      YoungCell.row a.1 = YoungCell.row b.1 ->
      YoungCell.col a.1 < YoungCell.col b.1 ->
      tableauDeleteMaxEntry T hu a < tableauDeleteMaxEntry T hu b := by
  exact tableauDeleteMaxEntry_row_strict T hu

/-- Lemma 5.15 set-level component: deleted entries remain column-strict. -/
theorem S05_Lem5_15_deleteMaxEntry_col_strict {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) {u : YoungCell lam}
    (hu : TableauMaxAt T u) :
    forall {a b : YoungCellExcept u},
      YoungCell.col a.1 = YoungCell.col b.1 ->
      YoungCell.row a.1 < YoungCell.row b.1 ->
      tableauDeleteMaxEntry T hu a < tableauDeleteMaxEntry T hu b := by
  exact tableauDeleteMaxEntry_col_strict T hu

/-- Lemma 5.15 set-level component: deleting the max cell gives a standard
tableau on the remaining cell set. -/
def S05_Lem5_15_deleteMaxAsStandardDeletedTableau {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) {u : YoungCell lam}
    (hu : TableauMaxAt T u) :
    StandardDeletedTableau u :=
  deleteMaxAsStandardDeletedTableau T hu

/-- Lemma 5.15 set-level component: parent cells other than the deleted corner
are equivalent to child cells. -/
def S05_Lem5_15_youngCellExceptEquivChildOfOneBoxChildRow
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (u : YoungCell lam)
    (hu_row : YoungCell.row u = r)
    (hu_col : YoungCell.col u = youngRow mu r) :
    YoungCellExcept u ≃ YoungCell mu :=
  youngCellExceptEquivChildOfOneBoxChildRow h hr u hu_row hu_col

/-- Lemma 5.15 set-level component: the parent-to-child cell equivalence
preserves rows. -/
theorem S05_Lem5_15_youngCellExceptEquivChild_to_row
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (u : YoungCell lam)
    (hu_row : YoungCell.row u = r)
    (hu_col : YoungCell.col u = youngRow mu r)
    (v : YoungCellExcept u) :
    YoungCell.row
        (S05_Lem5_15_youngCellExceptEquivChildOfOneBoxChildRow
          h hr u hu_row hu_col v)
      = YoungCell.row v.1 := by
  exact youngCellExceptEquivChild_to_row h hr u hu_row hu_col v

/-- Lemma 5.15 set-level component: the parent-to-child cell equivalence
preserves columns. -/
theorem S05_Lem5_15_youngCellExceptEquivChild_to_col
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (u : YoungCell lam)
    (hu_row : YoungCell.row u = r)
    (hu_col : YoungCell.col u = youngRow mu r)
    (v : YoungCellExcept u) :
    YoungCell.col
        (S05_Lem5_15_youngCellExceptEquivChildOfOneBoxChildRow
          h hr u hu_row hu_col v)
      = YoungCell.col v.1 := by
  exact youngCellExceptEquivChild_to_col h hr u hu_row hu_col v

/-- Lemma 5.15 set-level component: the child-to-parent inverse cell
equivalence preserves rows. -/
theorem S05_Lem5_15_youngCellExceptEquivChild_symm_row
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (u : YoungCell lam)
    (hu_row : YoungCell.row u = r)
    (hu_col : YoungCell.col u = youngRow mu r)
    (w : YoungCell mu) :
    YoungCell.row
        ((S05_Lem5_15_youngCellExceptEquivChildOfOneBoxChildRow
          h hr u hu_row hu_col).symm w).1
      = YoungCell.row w := by
  exact youngCellExceptEquivChild_symm_row h hr u hu_row hu_col w

/-- Lemma 5.15 set-level component: the child-to-parent inverse cell
equivalence preserves columns. -/
theorem S05_Lem5_15_youngCellExceptEquivChild_symm_col
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (u : YoungCell lam)
    (hu_row : YoungCell.row u = r)
    (hu_col : YoungCell.col u = youngRow mu r)
    (w : YoungCell mu) :
    YoungCell.col
        ((S05_Lem5_15_youngCellExceptEquivChildOfOneBoxChildRow
          h hr u hu_row hu_col).symm w).1
      = YoungCell.col w := by
  exact youngCellExceptEquivChild_symm_col h hr u hu_row hu_col w

/-- Lemma 5.15 set-level component: deleting the maximum cell gives a standard
tableau of the one-box child shape. -/
def S05_Lem5_15_deleteMaxAsStandardYoungTableauOfOneBoxChildRow
    {n : Nat} {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (u : YoungCell lam)
    (hu_row : YoungCell.row u = r)
    (hu_col : YoungCell.col u = youngRow mu r)
    (T : StandardYoungTableau lam)
    (hu : TableauMaxAt T u) :
    StandardYoungTableau mu :=
  deleteMaxAsStandardYoungTableauOfOneBoxChildRow h hr u hu_row hu_col T hu

/-- Lemma 5.15 set-level inverse: insert the maximum entry in the deleted
corner. -/
def S05_Lem5_15_insertMaxAsStandardYoungTableauOfOneBoxChildRow
    {n : Nat} {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (S : StandardYoungTableau mu) :
    StandardYoungTableau lam :=
  insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr S

/-- Lemma 5.15 set-level component: the deleted corner has the row prescribed
by the one-box row form. -/
theorem S05_Lem5_15_deletedCornerCell_row
    {n : Nat} {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t) :
    YoungCell.row (deletedCornerCellOfOneBoxChildRow h hr) = r := by
  exact deletedCornerCell_row h hr

/-- Lemma 5.15 set-level component: the deleted corner is the final column of
the removed row. -/
theorem S05_Lem5_15_deletedCornerCell_col
    {n : Nat} {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t) :
    YoungCell.col (deletedCornerCellOfOneBoxChildRow h hr) = youngRow mu r := by
  exact deletedCornerCell_col h hr

theorem S05_Lem5_15_insertMax_tableauMaxAt_deletedCorner
    {n : Nat} {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (S : StandardYoungTableau mu) :
    TableauMaxAt
      (S05_Lem5_15_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr S)
      (deletedCornerCellOfOneBoxChildRow h hr) := by
  exact insertMax_tableauMaxAt_deletedCorner h hr S

/-- Lemma 5.15 set-level component: insertion puts the new maximum entry at
the deleted corner. -/
theorem S05_Lem5_15_insertMax_entry_deletedCorner
    {n : Nat} {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (S : StandardYoungTableau mu) :
    (S05_Lem5_15_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr S).entry
      (deletedCornerCellOfOneBoxChildRow h hr) = Fin.last n := by
  exact insertMaxAsStandardYoungTableau_entry_deletedCorner h hr S

/-- Lemma 5.15 set-level component: away from the deleted corner, insertion
agrees with the child tableau through the parent-child cell equivalence. -/
theorem S05_Lem5_15_insertMax_entry_ne_deletedCorner
    {n : Nat} {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (S : StandardYoungTableau mu)
    (v : YoungCell lam)
    (hv : v ≠ deletedCornerCellOfOneBoxChildRow h hr) :
    (S05_Lem5_15_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr S).entry v =
      Fin.castSucc
        (S.entry
          (youngCellExceptEquivChildOfOneBoxChildRow h hr
            (deletedCornerCellOfOneBoxChildRow h hr)
            (deletedCornerCell_row h hr)
            (deletedCornerCell_col h hr) ⟨v, hv⟩)) := by
  exact insertMaxAsStandardYoungTableau_entry_ne_deletedCorner h hr S hv

/-- Lemma 5.15 set-level component: away from the deleted corner, inserted
entries are strictly below the new maximum. -/
theorem S05_Lem5_15_insertMax_entry_lt_last_of_ne_deletedCorner
    {n : Nat} {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (S : StandardYoungTableau mu)
    {v : YoungCell lam}
    (hv : v ≠ deletedCornerCellOfOneBoxChildRow h hr) :
    (S05_Lem5_15_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr S).entry v <
      Fin.last n := by
  exact insertedMaxEntry_lt_last_of_ne_deletedCorner h hr S hv

theorem S05_Lem5_15_delete_insert
    {n : Nat} {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (S : StandardYoungTableau mu) :
    deleteMaxAsStandardYoungTableauOfOneBoxChildRow
        h hr
        (deletedCornerCellOfOneBoxChildRow h hr)
        (deletedCornerCell_row h hr)
        (deletedCornerCell_col h hr)
        (insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr S)
        (insertMax_tableauMaxAt_deletedCorner h hr S)
      = S := by
  exact deleteMax_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr S

theorem S05_Lem5_15_insert_delete
    {n : Nat} {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (T : StandardYoungTableau lam)
    (hu : TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h hr)) :
    insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr
      (deleteMaxAsStandardYoungTableauOfOneBoxChildRow
        h hr
        (deletedCornerCellOfOneBoxChildRow h hr)
        (deletedCornerCell_row h hr)
        (deletedCornerCell_col h hr)
        T hu)
      = T := by
  exact insertMax_deleteMaxAsStandardYoungTableauOfOneBoxChildRow h hr T hu

def S05_Lem5_15_oneBoxDeletionTableauxEquivChildTableauxOfOneBoxChildRow
    {n : Nat} {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t) :
    {T : StandardYoungTableau lam //
      TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h hr)}
      ≃ StandardYoungTableau mu :=
  oneBoxDeletionTableauxEquivChildTableauxOfOneBoxChildRow h hr

/-- Coordinate functions on the parent tableaux whose maximum entry is in the
deleted corner. -/
abbrev S05_Lem5_15_OneBoxDeletionCoordinateSpace
    {n : Nat} {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t) :=
    {T : StandardYoungTableau lam //
      TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h hr)} -> ℝ

/-- The coordinate inner product on the one-box deletion fiber. -/
def S05_Lem5_15_oneBoxDeletionInner
    {n : Nat} {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (f g : S05_Lem5_15_OneBoxDeletionCoordinateSpace h hr) : ℝ :=
  ∑ T : {T : StandardYoungTableau lam //
      TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h hr)}, f T * g T

/-- The coordinate map induced by deleting the maximum-entry box. -/
def S05_Lem5_15_deletionCoordinateMap
    {n : Nat} {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (f : S05_Lem5_15_OneBoxDeletionCoordinateSpace h hr) :
    TableauSpace mu :=
  fun S =>
    f ((S05_Lem5_15_oneBoxDeletionTableauxEquivChildTableauxOfOneBoxChildRow
      h hr).symm S)

/-- Lemma 5.15 coordinate form: the deletion equivalence preserves the finite
coordinate inner product. -/
theorem S05_Lem5_15_deletionCoordinateMap_inner
    {n : Nat} {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (f g : S05_Lem5_15_OneBoxDeletionCoordinateSpace h hr) :
    tableauInner
        (S05_Lem5_15_deletionCoordinateMap h hr f)
        (S05_Lem5_15_deletionCoordinateMap h hr g)
      =
    S05_Lem5_15_oneBoxDeletionInner h hr f g := by
  classical
  let e := S05_Lem5_15_oneBoxDeletionTableauxEquivChildTableauxOfOneBoxChildRow
    h hr
  change
    (∑ S : StandardYoungTableau mu, f (e.symm S) * g (e.symm S)) =
      ∑ T : {T : StandardYoungTableau lam //
        TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h hr)}, f T * g T
  exact Fintype.sum_equiv e.symm
    (fun S : StandardYoungTableau mu => f (e.symm S) * g (e.symm S))
    (fun T : {T : StandardYoungTableau lam //
        TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h hr)} => f T * g T)
    (fun _ => rfl)

end DictatorshipTesting
