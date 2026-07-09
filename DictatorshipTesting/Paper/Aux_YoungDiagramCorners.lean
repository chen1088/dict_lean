import DictatorshipTesting.Paper.Defs

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Aux_StandardYoungTableaux`
- `DictatorshipTesting.Paper.S05_Def5_02_RemovableCorners`
- `DictatorshipTesting.Paper.S05_Def5_11_TwoBoxRemovals`
- `DictatorshipTesting.Paper.S05_Def5_13_OneBoxRemovals`
-/


/-!
# One-box removals and Young-diagram rows

This file contains elementary row combinatorics for Young diagrams.  It does
not use representation theory: a one-box child has row-length difference
concentrated in exactly one row.
-/

noncomputable section

namespace DictatorshipTesting

/-- The stored row lengths of a Young diagram sum to its size, restated over
`Finset.range`. -/
theorem youngRow_sum_range {n : Nat} (lam : YoungDiagram n) :
    (Finset.range n).sum (fun i => youngRow lam i) = n := by
  have hfin : (Finset.univ.sum (fun i : Fin n => youngRow lam i)) =
      ((Finset.range n).sum (fun i => youngRow lam i)) := by
    exact Fin.sum_univ_eq_sum_range (fun i => youngRow lam i) n
  rw [hfin.symm]
  simpa [youngRow] using lam.sum_rows

/-- Summing the extended row lengths of a diagram of size `k` over one extra
row still gives `k`. -/
theorem youngRow_sum_range_succ {k : Nat} (mu : YoungDiagram k) :
    (Finset.range (k + 1)).sum (fun i => youngRow mu i) = k := by
  rw [Finset.sum_range_succ]
  rw [youngRow_sum_range mu]
  simp [youngRow]

/-- Summing the extended row lengths of a diagram of size `k` over two extra
rows still gives `k`. -/
theorem youngRow_sum_range_add_two {k : Nat} (mu : YoungDiagram k) :
    (Finset.range (k + 2)).sum (fun i => youngRow mu i) = k := by
  rw [show k + 2 = k + 1 + 1 by omega]
  rw [Finset.sum_range_succ]
  rw [youngRow_sum_range_succ mu]
  simp [youngRow]

/-- Extended row lengths are nonincreasing. -/
theorem youngRow_succ_le {n : Nat} (lam : YoungDiagram n) (r : Nat) :
    youngRow lam (r + 1) <= youngRow lam r := by
  by_cases hsucc : r + 1 < n
  · have hr : r < n := by omega
    have hmono := lam.nonincreasing
      (i := Fin.mk r hr) (j := Fin.mk (r + 1) hsucc) (by
        change r <= r + 1
        omega)
    simpa [youngRow, hr, hsucc] using hmono
  · have hzero : youngRow lam (r + 1) = 0 := by
      simp [youngRow, hsucc]
    rw [hzero]
    exact Nat.zero_le _

/-- A row of a Young diagram is removable when deleting its final box still
leaves a Young diagram. Rows are zero-indexed. -/
def IsRemovableRow {n : Nat} (lam : YoungDiagram n) (r : Nat) : Prop :=
  youngRow lam (r + 1) < youngRow lam r

/-- A box of a Young diagram, in zero-indexed row-column coordinates. -/
def IsYoungBox {n : Nat} (lam : YoungDiagram n) (u : Nat × Nat) : Prop :=
  u.2 < youngRow lam u.1

/-- A removable corner box is the final box of a row whose deletion leaves a
Young diagram. Coordinates are zero-indexed. -/
def IsRemovableCornerBox {n : Nat} (lam : YoungDiagram n) (u : Nat × Nat) : Prop :=
  IsYoungBox lam u ∧
    u.2 + 1 = youngRow lam u.1 ∧
    youngRow lam (u.1 + 1) <= u.2

/-- If a natural-valued finite sum is `1`, then exactly one summand is `1` and
all other summands are `0`. -/
theorem exists_unique_one_of_sum_eq_one {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α -> Nat) (hsum : s.sum f = 1) :
    exists a, a ∈ s ∧ f a = 1 ∧
      forall b, b ∈ s -> b ≠ a -> f b = 0 := by
  classical
  have hexists : exists a, a ∈ s ∧ f a ≠ 0 := by
    by_contra hnone
    have hnone_zero : forall a, a ∈ s -> f a = 0 := by
      intro a ha
      by_contra hfa
      exact hnone ⟨a, ha, hfa⟩
    have hzero : s.sum f = 0 := by
      exact (Finset.sum_eq_zero_iff).mpr hnone_zero
    omega
  rcases hexists with ⟨a, ha, hfa_ne⟩
  have hfa_le : f a <= 1 := by
    have hle := Finset.single_le_sum
      (s := s) (f := f) (fun i _hi => Nat.zero_le (f i)) ha
    simpa [hsum] using hle
  have hfa_pos : 0 < f a := Nat.pos_of_ne_zero hfa_ne
  have hfa : f a = 1 := by
    omega
  have herase_sum : (s.erase a).sum f = 0 := by
    have hsplit := Finset.sum_erase_add s f ha
    have hsplit' : (s.erase a).sum f + 1 = 1 := by
      simpa [hsum, hfa] using hsplit
    omega
  have herase_zero :
      forall b, b ∈ s.erase a -> f b = 0 := by
    exact (Finset.sum_eq_zero_iff).mp herase_sum
  refine ⟨a, ha, hfa, ?_⟩
  intro b hb hba
  exact herase_zero b (Finset.mem_erase.mpr ⟨hba, hb⟩)

/-- For a one-box child, the total row-length difference is `1`. -/
theorem sum_row_diff_of_oneBoxChild
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : IsOneBoxChild lam mu) :
    (Finset.range n).sum (fun i => youngRow lam i - youngRow mu i) = 1 := by
  rcases h with ⟨hk, hsub⟩
  have hrow_le : forall i, i < n -> youngRow mu i <= youngRow lam i := by
    intro i hi
    simpa using hsub (Fin.mk i hi)
  have hsumsub := Finset.sum_tsub_distrib (Finset.range n)
    (f := fun i => youngRow lam i)
    (g := fun i => youngRow mu i)
    (by
      intro i hi
      exact hrow_le i (Finset.mem_range.mp hi))
  rw [hsumsub]
  rw [youngRow_sum_range lam]
  have hmu : (Finset.range n).sum (fun i => youngRow mu i) = k := by
    rw [hk.symm]
    exact youngRow_sum_range_succ mu
  rw [hmu]
  omega

/-- For a two-box subdiagram with size drop `2`, the total row-length
difference is `2`. -/
theorem sum_row_diff_of_twoBoxSubdiagram
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (hk : k + 2 = n) (hsub : IsYoungSubdiagram mu lam) :
    (Finset.range n).sum (fun i => youngRow lam i - youngRow mu i) = 2 := by
  have hrow_le : forall i, i < n -> youngRow mu i <= youngRow lam i := by
    intro i hi
    simpa using hsub (Fin.mk i hi)
  have hsumsub := Finset.sum_tsub_distrib (Finset.range n)
    (f := fun i => youngRow lam i)
    (g := fun i => youngRow mu i)
    (by
      intro i hi
      exact hrow_le i (Finset.mem_range.mp hi))
  rw [hsumsub]
  rw [youngRow_sum_range lam]
  have hmu : (Finset.range n).sum (fun i => youngRow mu i) = k := by
    rw [hk.symm]
    exact youngRow_sum_range_add_two mu
  rw [hmu]
  omega

/-- For a horizontal two-strip child, the total row-length difference is `2`. -/
theorem sum_row_diff_of_horizontalTwoStripChild
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : IsHorizontalTwoStripChild lam mu) :
    (Finset.range n).sum (fun i => youngRow lam i - youngRow mu i) = 2 := by
  exact sum_row_diff_of_twoBoxSubdiagram h.1 h.2.1

/-- For a vertical two-strip child, the total row-length difference is `2`. -/
theorem sum_row_diff_of_verticalTwoStripChild
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : IsVerticalTwoStripChild lam mu) :
    (Finset.range n).sum (fun i => youngRow lam i - youngRow mu i) = 2 := by
  exact sum_row_diff_of_twoBoxSubdiagram h.1 h.2.1

/-- Any two-strip child is rowwise bounded by its parent. -/
theorem row_le_parent_of_twoBoxSubdiagram
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (hk : k + 2 = n) (hsub : IsYoungSubdiagram mu lam) (i : Nat) :
    youngRow mu i <= youngRow lam i := by
  by_cases hi : i < n
  · exact hsub (Fin.mk i hi)
  · have hmu_not_lt : ¬ i < k := by omega
    simp [youngRow, hi, hmu_not_lt]

/-- A horizontal two-strip child is rowwise bounded by its parent. -/
theorem row_le_parent_of_horizontalTwoStripChild
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : IsHorizontalTwoStripChild lam mu) (i : Nat) :
    youngRow mu i <= youngRow lam i :=
  row_le_parent_of_twoBoxSubdiagram h.1 h.2.1 i

/-- A vertical two-strip child is rowwise bounded by its parent. -/
theorem row_le_parent_of_verticalTwoStripChild
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : IsVerticalTwoStripChild lam mu) (i : Nat) :
    youngRow mu i <= youngRow lam i :=
  row_le_parent_of_twoBoxSubdiagram h.1 h.2.1 i

/-- Horizontal two-strip row condition: the next parent row is bounded by the
current child row. -/
theorem next_parent_row_le_child_row_of_horizontalTwoStripChild
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : IsHorizontalTwoStripChild lam mu) (i : Nat) :
    youngRow lam (i + 1) <= youngRow mu i := by
  rcases h with ⟨hk, hsub, hhorizontal⟩
  by_cases hi : i < n
  · exact hhorizontal (Fin.mk i hi)
  · have hsucc_not_lt : ¬ i + 1 < n := by omega
    simp [youngRow, hsucc_not_lt]

/-- Vertical two-strip row condition: every parent row exceeds the child row by
at most one. -/
theorem parent_row_le_child_row_add_one_of_verticalTwoStripChild
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : IsVerticalTwoStripChild lam mu) (i : Nat) :
    youngRow lam i <= youngRow mu i + 1 := by
  rcases h with ⟨hk, hsub, hvertical⟩
  by_cases hi : i < n
  · exact hvertical (Fin.mk i hi)
  · simp [youngRow, hi]

/-- In a vertical two-strip child, each row loses at most one box. -/
theorem row_diff_le_one_of_verticalTwoStripChild
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : IsVerticalTwoStripChild lam mu) (i : Nat) :
    youngRow lam i - youngRow mu i <= 1 := by
  have hle := parent_row_le_child_row_add_one_of_verticalTwoStripChild h i
  omega

/-- For a one-box child `mu` of `lam`, the row-length difference is
concentrated in one row. -/
theorem exists_unique_row_of_oneBoxChild
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : IsOneBoxChild lam mu) :
    exists r : Nat,
      youngRow lam r = youngRow mu r + 1 ∧
      forall s : Nat, s ≠ r -> youngRow lam s = youngRow mu s := by
  rcases h with ⟨hk, hsub⟩
  have hchild : IsOneBoxChild lam mu := ⟨hk, hsub⟩
  have hrow_le : forall i, i < n -> youngRow mu i <= youngRow lam i := by
    intro i hi
    simpa using hsub (Fin.mk i hi)
  have hdiff_sum :
      (Finset.range n).sum (fun i => youngRow lam i - youngRow mu i) = 1 :=
    sum_row_diff_of_oneBoxChild hchild
  rcases exists_unique_one_of_sum_eq_one
      (Finset.range n)
      (fun i => youngRow lam i - youngRow mu i)
      hdiff_sum with ⟨r, hr_mem, hdiff_r, hdiff_other⟩
  have hr_lt : r < n := Finset.mem_range.mp hr_mem
  have hrow_r_le : youngRow mu r <= youngRow lam r := hrow_le r hr_lt
  refine ⟨r, ?_, ?_⟩
  · omega
  · intro s hsr
    by_cases hs_lt : s < n
    · have hdiff_s :
          youngRow lam s - youngRow mu s = 0 :=
        hdiff_other s (Finset.mem_range.mpr hs_lt) hsr
      have hrow_s_le : youngRow mu s <= youngRow lam s := hrow_le s hs_lt
      omega
    · have hlam_zero : youngRow lam s = 0 := by
        simp [youngRow, hs_lt]
      have hmu_not_lt : ¬ s < k := by
        omega
      have hmu_zero : youngRow mu s = 0 := by
        simp [youngRow, hmu_not_lt]
      rw [hlam_zero, hmu_zero]

/-- For a one-box child `mu` of `lam`, the changed row is unique. -/
theorem existsUnique_row_of_oneBoxChild
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : IsOneBoxChild lam mu) :
    ∃! r : Nat,
      youngRow lam r = youngRow mu r + 1 ∧
      forall s : Nat, s ≠ r -> youngRow lam s = youngRow mu s := by
  rcases exists_unique_row_of_oneBoxChild h with ⟨r, hr_eq, hr_other⟩
  refine ⟨r, ⟨hr_eq, hr_other⟩, ?_⟩
  intro t ht
  by_contra htr
  have h_eq_from_t : youngRow lam r = youngRow mu r :=
    ht.2 r (Ne.symm htr)
  omega

/-- In a one-box child, the changed row is removable in the parent. -/
theorem isRemovableRow_of_oneBoxChild_row
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (_h : IsOneBoxChild lam mu)
    {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall s : Nat, s ≠ r -> youngRow lam s = youngRow mu s) :
    IsRemovableRow lam r := by
  unfold IsRemovableRow
  have hnext_eq : youngRow lam (r + 1) = youngRow mu (r + 1) := by
    exact hr.2 (r + 1) (by omega)
  have hmu_succ_le : youngRow mu (r + 1) <= youngRow mu r :=
    youngRow_succ_le mu r
  rw [hnext_eq, hr.1]
  omega

/-- A one-box child removes a box from a removable row of the parent. -/
theorem exists_removableRow_of_oneBoxChild
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : IsOneBoxChild lam mu) :
    exists r : Nat,
      IsRemovableRow lam r ∧
      youngRow lam r = youngRow mu r + 1 ∧
      forall s : Nat, s ≠ r -> youngRow lam s = youngRow mu s := by
  rcases exists_unique_row_of_oneBoxChild h with ⟨r, hr_eq, hr_other⟩
  exact ⟨r, isRemovableRow_of_oneBoxChild_row h ⟨hr_eq, hr_other⟩,
    hr_eq, hr_other⟩

/-- The final box of a removable row is a removable corner box. -/
theorem removableCornerBox_of_removableRow
    {n : Nat} {lam : YoungDiagram n} {r : Nat}
    (hr : IsRemovableRow lam r) :
    IsRemovableCornerBox lam (r, youngRow lam r - 1) := by
  unfold IsRemovableCornerBox IsYoungBox IsRemovableRow at *
  have hpos : 0 < youngRow lam r := by
    omega
  constructor
  · change youngRow lam r - 1 < youngRow lam r
    omega
  constructor
  · change youngRow lam r - 1 + 1 = youngRow lam r
    omega
  · change youngRow lam (r + 1) <= youngRow lam r - 1
    omega

/-- A one-box child deletes a removable corner box of the parent. -/
theorem exists_removableCornerBox_of_oneBoxChild
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : IsOneBoxChild lam mu) :
    exists u : Nat × Nat,
      IsRemovableCornerBox lam u ∧
      u.2 = youngRow mu u.1 ∧
      youngRow lam u.1 = youngRow mu u.1 + 1 ∧
      forall s : Nat, s ≠ u.1 -> youngRow lam s = youngRow mu s := by
  rcases exists_removableRow_of_oneBoxChild h with
    ⟨r, hr_removable, hr_eq, hr_other⟩
  refine ⟨(r, youngRow mu r), ?_, rfl, hr_eq, ?_⟩
  · unfold IsRemovableCornerBox IsYoungBox IsRemovableRow at *
    constructor
    · change youngRow mu r < youngRow lam r
      omega
    constructor
    · change youngRow mu r + 1 = youngRow lam r
      omega
    · change youngRow lam (r + 1) <= youngRow mu r
      omega
  · intro s hs
    exact hr_other s hs

/-- A parent cell is either already a child cell, or it is the unique deleted
cell in the changed row. -/
theorem parent_cell_iff_child_cell_or_deleted_of_oneBoxChild_row
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (_h : IsOneBoxChild lam mu) {r s c : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t) :
    c < youngRow lam s <->
      c < youngRow mu s ∨ (s = r ∧ c = youngRow mu r) := by
  by_cases hsr : s = r
  · subst s
    rw [hr.1]
    constructor
    · intro hc
      by_cases hlt : c < youngRow mu r
      · exact Or.inl hlt
      · right
        constructor
        · rfl
        · omega
    · intro h
      rcases h with hlt | hdel
      · omega
      · rcases hdel with ⟨_, hc_eq⟩
        omega
  · rw [hr.2 s hsr]
    constructor
    · intro hc
      exact Or.inl hc
    · intro h
      rcases h with hc | hdel
      · exact hc
      · exact False.elim (hsr hdel.1)

/-- A child cell is exactly a parent cell that is not the unique deleted cell. -/
theorem child_cell_iff_parent_cell_not_deleted_of_oneBoxChild_row
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : IsOneBoxChild lam mu) {r s c : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t) :
    c < youngRow mu s <->
      c < youngRow lam s ∧ ¬ (s = r ∧ c = youngRow mu r) := by
  have hparent :=
    parent_cell_iff_child_cell_or_deleted_of_oneBoxChild_row
      (lam := lam) (mu := mu) h (r := r) (s := s) (c := c) hr
  constructor
  · intro hc
    constructor
    · exact hparent.mpr (Or.inl hc)
    · intro hdel
      rcases hdel with ⟨hsr, hc_eq⟩
      subst s
      omega
  · intro hp
    rcases hparent.mp hp.1 with hc | hdel
    · exact hc
    · exact False.elim (hp.2 hdel)

end DictatorshipTesting
