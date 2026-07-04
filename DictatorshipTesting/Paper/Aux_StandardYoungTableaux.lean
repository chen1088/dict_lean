import DictatorshipTesting.Paper.Aux_YoungDiagramCorners

/-!
# Standard Young tableaux

This file contains the concrete tableau vocabulary needed by Definition 5.9:
cells of a Young diagram, standard Young tableaux, and the set of tableaux whose
maximum entry lies in a specified cell.  It does not introduce the later
Hilbert-space/span version of the deletion spaces.
-/

noncomputable section

namespace DictatorshipTesting

/-- A cell of a Young diagram. -/
abbrev YoungCell {n : Nat} (lam : YoungDiagram n) :=
  {u : Fin n × Fin n // u ∈ youngCells lam}

namespace YoungCell

/-- Row coordinate of a Young cell. -/
def row {n : Nat} {lam : YoungDiagram n} (u : YoungCell lam) : Nat :=
  (u.1.1 : Nat)

/-- Column coordinate of a Young cell. -/
def col {n : Nat} {lam : YoungDiagram n} (u : YoungCell lam) : Nat :=
  (u.1.2 : Nat)

/-- A Young cell as a pair of natural coordinates. -/
def toNatPair {n : Nat} {lam : YoungDiagram n} (u : YoungCell lam) : Nat × Nat :=
  (row u, col u)

/-- A `YoungCell` is a box of the underlying Young diagram. -/
theorem isYoungBox {n : Nat} {lam : YoungDiagram n} (u : YoungCell lam) :
    IsYoungBox lam (toNatPair u) := by
  rcases u with ⟨⟨r, c⟩, hcell⟩
  simpa [toNatPair, row, col, IsYoungBox, youngCells]
    using (Finset.mem_filter.mp hcell).2

end YoungCell

/-- A standard Young tableau of shape `lam`, with entries `0, ..., n-1`.
This is the zero-indexed version of the paper's entries `1, ..., n`. -/
structure StandardYoungTableau {n : Nat} (lam : YoungDiagram n) where
  entry : YoungCell lam -> Fin n
  bijective : Function.Bijective entry
  row_strict :
    forall {u v : YoungCell lam},
      YoungCell.row u = YoungCell.row v ->
      YoungCell.col u < YoungCell.col v ->
      entry u < entry v
  col_strict :
    forall {u v : YoungCell lam},
      YoungCell.col u = YoungCell.col v ->
      YoungCell.row u < YoungCell.row v ->
      entry u < entry v

/-- The maximum entry of a tableau of size `n+1` is in cell `u`. -/
def TableauMaxAt {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (u : YoungCell lam) : Prop :=
  T.entry u = Fin.last n

/-- Set-level version of the one-box deletion space: tableaux whose maximum
entry lies in `u`. The Hilbert-space span will be added later. -/
def OneBoxDeletionTableaux {n : Nat} (lam : YoungDiagram (n + 1))
    (u : YoungCell lam) : Set (StandardYoungTableau lam) :=
  {T | TableauMaxAt T u}

/-- Membership in the set-level one-box deletion space is the maximum-entry
condition. -/
theorem mem_oneBoxDeletionTableaux_iff {n : Nat}
    {lam : YoungDiagram (n + 1)} {u : YoungCell lam}
    {T : StandardYoungTableau lam} :
    T ∈ OneBoxDeletionTableaux lam u <-> TableauMaxAt T u := by
  rfl

/-- Row lengths are bounded by the total size of the diagram. -/
theorem youngRow_le_size_aux {n : Nat} (lam : YoungDiagram n) (i : Nat) :
    youngRow lam i <= n := by
  unfold youngRow
  split
  · exact Nat.le_of_lt_succ (lam.row ⟨i, ‹i < n›⟩).isLt
  · exact Nat.zero_le _

/-- The maximum entry cell of a standard Young tableau exists uniquely. -/
theorem existsUnique_tableauMaxAt {n : Nat}
    {lam : YoungDiagram (n + 1)} (T : StandardYoungTableau lam) :
    ∃! u : YoungCell lam, TableauMaxAt T u := by
  rcases T.bijective.2 (Fin.last n) with ⟨u, hu⟩
  refine ⟨u, hu, ?_⟩
  intro v hv
  exact T.bijective.1 (by rw [hv, hu])

/-- A maximum-entry cell has no cell immediately to its right. -/
theorem no_cell_right_of_tableauMaxAt {n : Nat}
    {lam : YoungDiagram (n + 1)} (T : StandardYoungTableau lam)
    {u : YoungCell lam} (hu : TableauMaxAt T u) :
    ¬ YoungCell.col u + 1 < youngRow lam (YoungCell.row u) := by
  intro hright
  rcases u with ⟨⟨r, c⟩, hcell⟩
  have hright' : (c : Nat) + 1 < youngRow lam (r : Nat) := by
    simpa [YoungCell.row, YoungCell.col] using hright
  let cRight : Fin (n + 1) := ⟨(c : Nat) + 1, by
    have hrow_le : youngRow lam (r : Nat) <= n + 1 :=
      youngRow_le_size_aux lam (r : Nat)
    omega⟩
  let v : YoungCell lam := ⟨(r, cRight), by
    simp [youngCells, cRight, hright']⟩
  have hstrict : T.entry ⟨⟨r, c⟩, hcell⟩ < T.entry v := by
    apply T.row_strict
    · simp [YoungCell.row, v]
    · simp [YoungCell.col, v, cRight]
  have hltVal :
      (T.entry ⟨⟨r, c⟩, hcell⟩ : Nat) < (T.entry v : Nat) := hstrict
  have huVal : (T.entry ⟨⟨r, c⟩, hcell⟩ : Nat) = n := by
    simpa [TableauMaxAt] using congrArg Fin.val hu
  have hvBound : (T.entry v : Nat) < n + 1 := (T.entry v).isLt
  omega

/-- A maximum-entry cell has no cell immediately below it. -/
theorem no_cell_below_tableauMaxAt {n : Nat}
    {lam : YoungDiagram (n + 1)} (T : StandardYoungTableau lam)
    {u : YoungCell lam} (hu : TableauMaxAt T u) :
    ¬ YoungCell.col u < youngRow lam (YoungCell.row u + 1) := by
  intro hbelow
  rcases u with ⟨⟨r, c⟩, hcell⟩
  have hbelow' : (c : Nat) < youngRow lam ((r : Nat) + 1) := by
    simpa [YoungCell.row, YoungCell.col] using hbelow
  let rBelow : Fin (n + 1) := ⟨(r : Nat) + 1, by
    by_contra hnot
    have hzero : youngRow lam ((r : Nat) + 1) = 0 := by
      simp [youngRow, hnot]
    omega⟩
  let v : YoungCell lam := ⟨(rBelow, c), by
    simp [youngCells, rBelow, hbelow']⟩
  have hstrict : T.entry ⟨⟨r, c⟩, hcell⟩ < T.entry v := by
    apply T.col_strict
    · simp [YoungCell.col, v]
    · simp [YoungCell.row, v, rBelow]
  have hltVal :
      (T.entry ⟨⟨r, c⟩, hcell⟩ : Nat) < (T.entry v : Nat) := hstrict
  have huVal : (T.entry ⟨⟨r, c⟩, hcell⟩ : Nat) = n := by
    simpa [TableauMaxAt] using congrArg Fin.val hu
  have hvBound : (T.entry v : Nat) < n + 1 := (T.entry v).isLt
  omega

/-- If the maximum entry of a standard tableau is in `u`, then `u` is a
removable corner box. -/
theorem removableCornerBox_of_tableauMaxAt {n : Nat}
    {lam : YoungDiagram (n + 1)} (T : StandardYoungTableau lam)
    {u : YoungCell lam} (hu : TableauMaxAt T u) :
    IsRemovableCornerBox lam (YoungCell.toNatPair u) := by
  constructor
  · exact YoungCell.isYoungBox u
  constructor
  · have hbox : YoungCell.col u < youngRow lam (YoungCell.row u) := by
      simpa [YoungCell.toNatPair, IsYoungBox] using YoungCell.isYoungBox u
    have hno_right := no_cell_right_of_tableauMaxAt T hu
    change YoungCell.col u + 1 = youngRow lam (YoungCell.row u)
    omega
  · have hno_below := no_cell_below_tableauMaxAt T hu
    change youngRow lam (YoungCell.row u + 1) <= YoungCell.col u
    omega

/-- The maximum entry of a standard tableau lies in a unique removable corner. -/
theorem existsUnique_removableCornerBox_tableauMaxAt {n : Nat}
    {lam : YoungDiagram (n + 1)} (T : StandardYoungTableau lam) :
    ∃! u : YoungCell lam,
      TableauMaxAt T u ∧ IsRemovableCornerBox lam (YoungCell.toNatPair u) := by
  rcases existsUnique_tableauMaxAt T with ⟨u, hu, huniq⟩
  refine ⟨u, ⟨hu, removableCornerBox_of_tableauMaxAt T hu⟩, ?_⟩
  intro v hv
  exact huniq v hv.1

/-- Cells other than a specified cell. -/
abbrev YoungCellExcept {n : Nat} {lam : YoungDiagram n} (u : YoungCell lam) :=
  {v : YoungCell lam // v ≠ u}

/-- After deleting the maximum-entry cell, the remaining entries lie in `Fin n`. -/
def tableauDeleteMaxEntry {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) {u : YoungCell lam}
    (hu : TableauMaxAt T u) :
    YoungCellExcept u -> Fin n :=
  fun v =>
    ⟨(T.entry v.1 : Nat), by
      have hnot_last : T.entry v.1 ≠ Fin.last n := by
        intro hlast
        have hvu : v.1 = u := T.bijective.1 (by rw [hlast, hu])
        exact v.2 hvu
      have hlt_succ : (T.entry v.1 : Nat) < n + 1 := (T.entry v.1).isLt
      have hnot_eq_n : (T.entry v.1 : Nat) ≠ n := by
        intro hn
        apply hnot_last
        exact Fin.ext (by simpa using hn)
      omega⟩

/-- The deletion map preserves the numeric value of each nonmaximum entry. -/
theorem tableauDeleteMaxEntry_val {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) {u : YoungCell lam}
    (hu : TableauMaxAt T u) (v : YoungCellExcept u) :
    (tableauDeleteMaxEntry T hu v : Nat) = (T.entry v.1 : Nat) := by
  rfl

/-- The set-level deletion map is injective. -/
theorem tableauDeleteMaxEntry_injective {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) {u : YoungCell lam}
    (hu : TableauMaxAt T u) :
    Function.Injective (tableauDeleteMaxEntry T hu) := by
  intro a b h
  apply Subtype.ext
  apply T.bijective.1
  apply Fin.ext
  have hval := congrArg Fin.val h
  simpa [tableauDeleteMaxEntry_val] using hval

/-- The set-level deletion map is surjective. -/
theorem tableauDeleteMaxEntry_surjective {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) {u : YoungCell lam}
    (hu : TableauMaxAt T u) :
    Function.Surjective (tableauDeleteMaxEntry T hu) := by
  intro y
  let target : Fin (n + 1) := Fin.castSucc y
  rcases T.bijective.2 target with ⟨v, hv⟩
  have hne : v ≠ u := by
    intro hvu
    have htarget_last : target = Fin.last n := by
      rw [← hv, hvu, hu]
    have hval := congrArg Fin.val htarget_last
    have hylt : (y : Nat) < n := y.isLt
    simp [target] at hval
    omega
  refine ⟨⟨v, hne⟩, ?_⟩
  apply Fin.ext
  have hvVal := congrArg Fin.val hv
  simpa [tableauDeleteMaxEntry_val, target] using hvVal

/-- Deleting the maximum-entry cell gives a bijection from the remaining cells
to `Fin n`. -/
theorem tableauDeleteMaxEntry_bijective {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) {u : YoungCell lam}
    (hu : TableauMaxAt T u) :
    Function.Bijective (tableauDeleteMaxEntry T hu) := by
  exact ⟨tableauDeleteMaxEntry_injective T hu,
    tableauDeleteMaxEntry_surjective T hu⟩

/-- Deleted entries remain row-strict on the remaining cells. -/
theorem tableauDeleteMaxEntry_row_strict {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) {u : YoungCell lam}
    (hu : TableauMaxAt T u) :
    forall {a b : YoungCellExcept u},
      YoungCell.row a.1 = YoungCell.row b.1 ->
      YoungCell.col a.1 < YoungCell.col b.1 ->
      tableauDeleteMaxEntry T hu a < tableauDeleteMaxEntry T hu b := by
  intro a b hrow hcol
  have hstrict : T.entry a.1 < T.entry b.1 := T.row_strict hrow hcol
  change (tableauDeleteMaxEntry T hu a : Nat) <
    (tableauDeleteMaxEntry T hu b : Nat)
  rw [tableauDeleteMaxEntry_val T hu a, tableauDeleteMaxEntry_val T hu b]
  exact hstrict

/-- Deleted entries remain column-strict on the remaining cells. -/
theorem tableauDeleteMaxEntry_col_strict {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) {u : YoungCell lam}
    (hu : TableauMaxAt T u) :
    forall {a b : YoungCellExcept u},
      YoungCell.col a.1 = YoungCell.col b.1 ->
      YoungCell.row a.1 < YoungCell.row b.1 ->
      tableauDeleteMaxEntry T hu a < tableauDeleteMaxEntry T hu b := by
  intro a b hcol hrow
  have hstrict : T.entry a.1 < T.entry b.1 := T.col_strict hcol hrow
  change (tableauDeleteMaxEntry T hu a : Nat) <
    (tableauDeleteMaxEntry T hu b : Nat)
  rw [tableauDeleteMaxEntry_val T hu a, tableauDeleteMaxEntry_val T hu b]
  exact hstrict

/-- A standard tableau on the cell set obtained by deleting one cell. -/
structure StandardDeletedTableau {n : Nat}
    {lam : YoungDiagram (n + 1)} (u : YoungCell lam) where
  entry : YoungCellExcept u -> Fin n
  bijective : Function.Bijective entry
  row_strict :
    forall {a b : YoungCellExcept u},
      YoungCell.row a.1 = YoungCell.row b.1 ->
      YoungCell.col a.1 < YoungCell.col b.1 ->
      entry a < entry b
  col_strict :
    forall {a b : YoungCellExcept u},
      YoungCell.col a.1 = YoungCell.col b.1 ->
      YoungCell.row a.1 < YoungCell.row b.1 ->
      entry a < entry b

/-- Delete the maximum-entry cell of a standard tableau, as a standard tableau
on the remaining cell set. -/
def deleteMaxAsStandardDeletedTableau {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) {u : YoungCell lam}
    (hu : TableauMaxAt T u) :
    StandardDeletedTableau u where
  entry := tableauDeleteMaxEntry T hu
  bijective := tableauDeleteMaxEntry_bijective T hu
  row_strict := tableauDeleteMaxEntry_row_strict T hu
  col_strict := tableauDeleteMaxEntry_col_strict T hu

end DictatorshipTesting
