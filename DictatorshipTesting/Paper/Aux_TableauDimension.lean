import DictatorshipTesting.Paper.Aux_StandardYoungTableaux

/-!
# Tableau-count dimension

This helper file defines an assumption-free dimension proxy by counting standard
Young tableaux.  It is parallel to the hook-length `youngDim` definition in
`Defs.lean`; no Specht-module dimension theorem is asserted here.
-/

noncomputable section

namespace DictatorshipTesting

noncomputable instance standardYoungTableauFintype {n : Nat}
    (lam : YoungDiagram n) : Fintype (StandardYoungTableau lam) := by
  classical
  exact Fintype.ofInjective
    (fun T : StandardYoungTableau lam => T.entry)
    (by
      intro T S h
      exact standardYoungTableau_ext_entry (by
        intro u
        exact congrFun h u))

noncomputable instance tableauMaxAtSubtypeFintype {n : Nat}
    {lam : YoungDiagram (n + 1)} (u : YoungCell lam) :
    Fintype {T : StandardYoungTableau lam // TableauMaxAt T u} := by
  classical
  infer_instance

/-- Assumption-free tableau-count dimension. -/
def tableauDimNat {n : Nat} (lam : YoungDiagram n) : Nat :=
  Fintype.card (StandardYoungTableau lam)

/-- Real-valued tableau-count dimension. -/
def tableauDim {n : Nat} (lam : YoungDiagram n) : ℝ :=
  tableauDimNat lam

theorem tableauDimNat_eq_card {n : Nat} (lam : YoungDiagram n) :
    tableauDimNat lam = Fintype.card (StandardYoungTableau lam) := by
  rfl

theorem tableauDim_nonneg {n : Nat} (lam : YoungDiagram n) :
    0 <= tableauDim lam := by
  simp [tableauDim]

theorem card_tableaux_maxAt_deletedCorner_eq_child
    {n : Nat} {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t) :
    Fintype.card
        {T : StandardYoungTableau lam //
          TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h hr)}
      =
    Fintype.card (StandardYoungTableau mu) := by
  classical
  exact Fintype.card_congr
    (oneBoxDeletionTableauxEquivChildTableauxOfOneBoxChildRow h hr)

theorem tableauDim_fixed_oneBoxChild
    {n : Nat} {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t) :
    ((Fintype.card
        {T : StandardYoungTableau lam //
          TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h hr)} : Nat) : ℝ)
      =
    tableauDim mu := by
  rw [tableauDim, tableauDimNat,
    card_tableaux_maxAt_deletedCorner_eq_child h hr]

theorem removableRow_lt_size {n : Nat} {lam : YoungDiagram (n + 1)}
    {r : Nat} (hr : IsRemovableRow lam r) :
    r < n + 1 := by
  by_contra h
  have hr0 : youngRow lam r = 0 := by
    simp [youngRow, h]
  have hsucc0 : youngRow lam (r + 1) = 0 := by
    have hsucc : ¬ r + 1 < n + 1 := by omega
    simp [youngRow, hsucc]
  unfold IsRemovableRow at hr
  omega

theorem removableRow_pos {n : Nat} {lam : YoungDiagram (n + 1)}
    {r : Nat} (hr : IsRemovableRow lam r) :
    0 < youngRow lam r := by
  unfold IsRemovableRow at hr
  omega

theorem youngRow_lt_size_of_removable_ne {n : Nat}
    {lam : YoungDiagram (n + 1)} {r i : Nat}
    (hr : IsRemovableRow lam r) (hi : i < n + 1) (hne : i ≠ r) :
    youngRow lam i < n + 1 := by
  have hle : youngRow lam i <= n + 1 := youngRow_le_size_aux lam i
  by_contra hnot
  have hi_eq : youngRow lam i = n + 1 := by omega
  have hr_lt : r < n + 1 := removableRow_lt_size hr
  have hr_pos : 0 < youngRow lam r := removableRow_pos hr
  have hsum := youngRow_sum_range lam
  have hi_mem : i ∈ Finset.range (n + 1) := Finset.mem_range.mpr hi
  have hsplit := Finset.sum_erase_add (Finset.range (n + 1))
    (fun j => youngRow lam j) hi_mem
  have herase_zero_sum :
      ((Finset.range (n + 1)).erase i).sum (fun j => youngRow lam j) = 0 := by
    rw [hsum, hi_eq] at hsplit
    omega
  have herase_zero :
      forall j, j ∈ (Finset.range (n + 1)).erase i -> youngRow lam j = 0 := by
    exact (Finset.sum_eq_zero_iff).mp herase_zero_sum
  have hr_mem_erase : r ∈ (Finset.range (n + 1)).erase i := by
    exact Finset.mem_erase.mpr ⟨by exact Ne.symm hne, Finset.mem_range.mpr hr_lt⟩
  have hr_zero := herase_zero r hr_mem_erase
  omega

theorem youngRow_last_eq_zero_of_removable_lt {n : Nat}
    {lam : YoungDiagram (n + 1)} {r : Nat}
    (hr : IsRemovableRow lam r) (hrn : r < n) :
    youngRow lam n = 0 := by
  by_contra hne
  have hlast_pos : 0 < youngRow lam n := Nat.pos_of_ne_zero hne
  have hsum := youngRow_sum_range lam
  have hlower :
      (Finset.range (n + 1)).sum
          (fun i => 1 + if i = r then 1 else 0) <=
        (Finset.range (n + 1)).sum (fun i => youngRow lam i) := by
    apply Finset.sum_le_sum
    intro i hi
    have hin : i <= n := by
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    by_cases hir : i = r
    · subst i
      have hsucc_le_last : youngRow lam n <= youngRow lam (r + 1) :=
        youngRow_le_of_le lam (by omega)
      unfold IsRemovableRow at hr
      simp
      omega
    · have hlast_le : youngRow lam n <= youngRow lam i :=
        youngRow_le_of_le lam hin
      simp [hir]
      omega
  have hleft :
      (Finset.range (n + 1)).sum
          (fun i => 1 + if i = r then 1 else 0) = n + 2 := by
    rw [Finset.sum_add_distrib]
    have hrle : r <= n := by omega
    simp [Finset.sum_const, hrle]
  rw [hleft, hsum] at hlower
  omega

theorem youngRow_last_eq_one_of_removable_not_lt {n : Nat}
    {lam : YoungDiagram (n + 1)} {r : Nat}
    (hr : IsRemovableRow lam r) (hrn : ¬ r < n) :
    youngRow lam n = 1 := by
  have hr_lt : r < n + 1 := removableRow_lt_size hr
  have hr_eq : r = n := by omega
  have hlast_pos : 0 < youngRow lam n := by
    simpa [hr_eq] using removableRow_pos hr
  have hsum := youngRow_sum_range lam
  have hlast_le_one : youngRow lam n <= 1 := by
    by_contra hnot
    have htwo : 2 <= youngRow lam n := by omega
    have hlower :
        (Finset.range (n + 1)).sum (fun _ => 2) <=
          (Finset.range (n + 1)).sum (fun i => youngRow lam i) := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i <= n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hlast_le : youngRow lam n <= youngRow lam i :=
        youngRow_le_of_le lam hin
      omega
    have hleft :
        (Finset.range (n + 1)).sum (fun _ => 2) = 2 * (n + 1) := by
      simp [Finset.sum_const, mul_comm]
    rw [hleft, hsum] at hlower
    omega
  omega

def deleteRemovableRowLength {n : Nat} (lam : YoungDiagram (n + 1))
    (r : Nat) (i : Nat) : Nat :=
  if i = r then youngRow lam r - 1 else youngRow lam i

theorem deleteRemovableRowLength_lt {n : Nat}
    (lam : YoungDiagram (n + 1)) {r i : Nat}
    (hr : IsRemovableRow lam r) (hi : i < n) :
    deleteRemovableRowLength lam r i < n + 1 := by
  unfold deleteRemovableRowLength
  by_cases hir : i = r
  · subst i
    have hle : youngRow lam r <= n + 1 := youngRow_le_size_aux lam r
    simp
    omega
  · have hi' : i < n + 1 := by omega
    simpa [hir] using youngRow_lt_size_of_removable_ne hr hi' hir

theorem deleteRemovableRowLength_monotone {n : Nat}
    (lam : YoungDiagram (n + 1)) {r i j : Nat}
    (hr : IsRemovableRow lam r) (hij : i <= j) :
    deleteRemovableRowLength lam r j <= deleteRemovableRowLength lam r i := by
  unfold deleteRemovableRowLength
  by_cases hir : i = r
  · subst i
    by_cases hjr : j = r
    · subst j
      simp
    · have hrj : r < j := by omega
      have hsucc_le_j : r + 1 <= j := by omega
      have hj_le_succ : youngRow lam j <= youngRow lam (r + 1) :=
        youngRow_le_of_le lam hsucc_le_j
      unfold IsRemovableRow at hr
      simp [hjr]
      omega
  · by_cases hjr : j = r
    · subst j
      have hr_le_i : youngRow lam r <= youngRow lam i :=
        youngRow_le_of_le lam hij
      simp [hir]
      omega
    · have hji : youngRow lam j <= youngRow lam i :=
        youngRow_le_of_le lam hij
      simp [hir, hjr]
      exact hji

theorem sum_deleteRemovableRowLength {n : Nat}
    (lam : YoungDiagram (n + 1)) {r : Nat}
    (hr : IsRemovableRow lam r) :
    (Finset.range n).sum (fun i => deleteRemovableRowLength lam r i) = n := by
  by_cases hrn : r < n
  · have hlast0 : youngRow lam n = 0 :=
      youngRow_last_eq_zero_of_removable_lt hr hrn
    have hsum := youngRow_sum_range lam
    rw [Finset.sum_range_succ] at hsum
    rw [hlast0] at hsum
    simp at hsum
    let s := Finset.range n
    have hsum_s : s.sum (fun i => youngRow lam i) = n + 1 := by
      simpa [s] using hsum
    have hrmem : r ∈ s := Finset.mem_range.mpr hrn
    have hsplit_del :=
      Finset.sum_erase_add s (fun i => deleteRemovableRowLength lam r i) hrmem
    have hsplit_orig :=
      Finset.sum_erase_add s (fun i => youngRow lam i) hrmem
    have herase_eq :
        (s.erase r).sum (fun i => deleteRemovableRowLength lam r i) =
          (s.erase r).sum (fun i => youngRow lam i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hir : i ≠ r := (Finset.mem_erase.mp hi).1
      simp [deleteRemovableRowLength, hir]
    have hdel_at : deleteRemovableRowLength lam r r = youngRow lam r - 1 := by
      simp [deleteRemovableRowLength]
    have hpos : 0 < youngRow lam r := removableRow_pos hr
    change s.sum (fun i => deleteRemovableRowLength lam r i) = n
    rw [← hsplit_del, herase_eq, hdel_at]
    rw [← hsplit_orig] at hsum_s
    omega
  · have hlast1 : youngRow lam n = 1 :=
      youngRow_last_eq_one_of_removable_not_lt hr hrn
    have hsum := youngRow_sum_range lam
    rw [Finset.sum_range_succ] at hsum
    rw [hlast1] at hsum
    have hfirst : (Finset.range n).sum (fun i => youngRow lam i) = n := by
      omega
    have hr_eq : r = n := by
      have hr_lt : r < n + 1 := removableRow_lt_size hr
      omega
    trans (Finset.range n).sum (fun i => youngRow lam i)
    · apply Finset.sum_congr rfl
      intro i hi
      have hir : i ≠ r := by
        have hin : i < n := Finset.mem_range.mp hi
        omega
      simp [deleteRemovableRowLength, hir]
    · exact hfirst

def deleteRemovableRowDiagram {n : Nat} (lam : YoungDiagram (n + 1))
    (r : Nat) (hr : IsRemovableRow lam r) : YoungDiagram n where
  row := fun i =>
    ⟨deleteRemovableRowLength lam r i,
      deleteRemovableRowLength_lt lam hr i.isLt⟩
  nonincreasing := by
    intro i j hij
    change deleteRemovableRowLength lam r j <= deleteRemovableRowLength lam r i
    exact deleteRemovableRowLength_monotone lam hr hij
  sum_rows := by
    have hsum := sum_deleteRemovableRowLength lam hr
    have hfin :
        (Finset.univ.sum
            (fun i : Fin n => deleteRemovableRowLength lam r i)) =
          (Finset.range n).sum
            (fun i => deleteRemovableRowLength lam r i) := by
      exact Fin.sum_univ_eq_sum_range
        (fun i => deleteRemovableRowLength lam r i) n
    rw [hfin]
    exact hsum

theorem youngRow_deleteRemovableRowDiagram_of_lt {n : Nat}
    (lam : YoungDiagram (n + 1)) {r : Nat}
    (hr : IsRemovableRow lam r) {i : Nat} (hi : i < n) :
    youngRow (deleteRemovableRowDiagram lam r hr) i =
      deleteRemovableRowLength lam r i := by
  simp [youngRow, deleteRemovableRowDiagram, hi]

theorem youngRow_deleteRemovableRowDiagram {n : Nat}
    (lam : YoungDiagram (n + 1)) {r : Nat}
    (hr : IsRemovableRow lam r) (i : Nat) :
    youngRow (deleteRemovableRowDiagram lam r hr) i =
      if i = r then youngRow lam r - 1 else youngRow lam i := by
  by_cases hi : i < n
  · rw [youngRow_deleteRemovableRowDiagram_of_lt lam hr hi]
    rfl
  · have hlhs : youngRow (deleteRemovableRowDiagram lam r hr) i = 0 := by
      simp [youngRow, hi]
    rw [hlhs]
    by_cases hir : i = r
    · subst i
      have hlast1 : youngRow lam n = 1 :=
        youngRow_last_eq_one_of_removable_not_lt hr hi
      have hr_eq : r = n := by
        have hr_size : r < n + 1 := removableRow_lt_size hr
        omega
      rw [hr_eq]
      simp [hlast1]
    · have hzero : youngRow lam i = 0 := by
        by_cases hi_succ : i < n + 1
        · have hr_lt : r < n := by
            have hr_size : r < n + 1 := removableRow_lt_size hr
            omega
          have hlast0 : youngRow lam n = 0 :=
            youngRow_last_eq_zero_of_removable_lt hr hr_lt
          have hin : i = n := by omega
          simpa [hin] using hlast0
        · simp [youngRow, hi_succ]
      simp [hir, hzero]

theorem deleteRemovableRowDiagram_isOneBoxChild {n : Nat}
    (lam : YoungDiagram (n + 1)) {r : Nat} (hr : IsRemovableRow lam r) :
    IsOneBoxChild lam (deleteRemovableRowDiagram lam r hr) := by
  refine ⟨rfl, ?_⟩
  intro i
  rw [youngRow_deleteRemovableRowDiagram lam hr i]
  by_cases hir : (i : Nat) = r
  · simp [hir]
  · simp [hir]

theorem row_form_deleteRemovableRowDiagram {n : Nat}
    (lam : YoungDiagram (n + 1)) {r : Nat} (hr : IsRemovableRow lam r) :
    youngRow lam r = youngRow (deleteRemovableRowDiagram lam r hr) r + 1 ∧
      forall t : Nat, t ≠ r ->
        youngRow lam t = youngRow (deleteRemovableRowDiagram lam r hr) t := by
  constructor
  · rw [youngRow_deleteRemovableRowDiagram lam hr r]
    simp
    have hpos : 0 < youngRow lam r := removableRow_pos hr
    omega
  · intro t ht
    rw [youngRow_deleteRemovableRowDiagram lam hr t]
    simp [ht]

theorem youngDiagram_ext_youngRow {n : Nat} {lam mu : YoungDiagram n}
    (h : ∀ i : Nat, youngRow lam i = youngRow mu i) :
    lam = mu := by
  cases lam
  cases mu
  congr
  funext i
  apply Fin.ext
  have hi : (i : Nat) < n := i.isLt
  have hrow := h i
  simp [youngRow, hi] at hrow
  exact hrow

abbrev RemovableRow {n : Nat} (lam : YoungDiagram (n + 1)) :=
  {r : Nat // IsRemovableRow lam r}

def oneBoxChildrenSized {n : Nat} (lam : YoungDiagram (n + 1)) :
    Finset (YoungDiagram n) := by
  classical
  exact Finset.univ.filter (fun mu : YoungDiagram n => IsOneBoxChild lam mu)

theorem mem_oneBoxChildrenSized_iff {n : Nat}
    (lam : YoungDiagram (n + 1)) (mu : YoungDiagram n) :
    mu ∈ oneBoxChildrenSized lam ↔ IsOneBoxChild lam mu := by
  classical
  simp [oneBoxChildrenSized]

def horizontalTwoStripChildrenSized {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) : Finset (YoungDiagram n) := by
  classical
  exact Finset.univ.filter (fun mu : YoungDiagram n =>
    IsHorizontalTwoStripChild lam mu)

def verticalTwoStripChildrenSized {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) : Finset (YoungDiagram n) := by
  classical
  exact Finset.univ.filter (fun mu : YoungDiagram n =>
    IsVerticalTwoStripChild lam mu)

theorem mem_horizontalTwoStripChildrenSized_iff {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (mu : YoungDiagram n) :
    mu ∈ horizontalTwoStripChildrenSized lam ↔
      IsHorizontalTwoStripChild lam mu := by
  classical
  simp [horizontalTwoStripChildrenSized]

theorem mem_verticalTwoStripChildrenSized_iff {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (mu : YoungDiagram n) :
    mu ∈ verticalTwoStripChildrenSized lam ↔
      IsVerticalTwoStripChild lam mu := by
  classical
  simp [verticalTwoStripChildrenSized]

abbrev TaggedTwoStripChildrenSized {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) :=
  Sum
    {mu : YoungDiagram n // mu ∈ horizontalTwoStripChildrenSized lam}
    {mu : YoungDiagram n // mu ∈ verticalTwoStripChildrenSized lam}

def taggedTwoStripChildDiagram {n : Nat}
    {lam : YoungDiagram ((n + 1) + 1)}
    (x : TaggedTwoStripChildrenSized lam) : YoungDiagram n :=
  match x with
  | Sum.inl h => h.1
  | Sum.inr v => v.1

theorem sum_taggedTwoStripChildrenSized {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) :
    (∑ x : TaggedTwoStripChildrenSized lam,
        tableauDim (taggedTwoStripChildDiagram x))
      =
    (horizontalTwoStripChildrenSized lam).sum (fun mu => tableauDim mu) +
      (verticalTwoStripChildrenSized lam).sum (fun mu => tableauDim mu) := by
  classical
  rw [Fintype.sum_sum_type]
  congr 1
  · rw [Finset.univ_eq_attach]
    exact Finset.sum_attach
      (horizontalTwoStripChildrenSized lam) (fun mu => tableauDim mu)
  · rw [Finset.univ_eq_attach]
    exact Finset.sum_attach
      (verticalTwoStripChildrenSized lam) (fun mu => tableauDim mu)

def twoStripRowDiff {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (mu : YoungDiagram n)
    (i : Nat) : Nat :=
  youngRow lam i - youngRow mu i

def positiveDiffRows {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (mu : YoungDiagram n) :
    Finset Nat :=
  (Finset.range ((n + 1) + 1)).filter
    (fun i => 0 < twoStripRowDiff lam mu i)

theorem mem_positiveDiffRows_iff {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (mu : YoungDiagram n)
    (i : Nat) :
    i ∈ positiveDiffRows lam mu ↔
      i < (n + 1) + 1 ∧ 0 < twoStripRowDiff lam mu i := by
  simp [positiveDiffRows]

theorem positiveDiffRows_nonempty_of_twoBoxSubdiagram {n : Nat}
    {lam : YoungDiagram ((n + 1) + 1)} {mu : YoungDiagram n}
    (hsub : IsYoungSubdiagram mu lam) :
    (positiveDiffRows lam mu).Nonempty := by
  classical
  by_contra hempty
  have hzero :
      ∀ i ∈ Finset.range ((n + 1) + 1),
        youngRow lam i - youngRow mu i = 0 := by
    intro i hi
    by_contra hne
    have hpos : 0 < twoStripRowDiff lam mu i := Nat.pos_of_ne_zero hne
    have hmem : i ∈ positiveDiffRows lam mu := by
      exact (mem_positiveDiffRows_iff lam mu i).mpr
        ⟨Finset.mem_range.mp hi, hpos⟩
    exact hempty ⟨i, hmem⟩
  have hsum_zero :
      (Finset.range ((n + 1) + 1)).sum
        (fun i => youngRow lam i - youngRow mu i) = 0 := by
    exact (Finset.sum_eq_zero_iff).mpr hzero
  have hsum_two :
      (Finset.range ((n + 1) + 1)).sum
        (fun i => youngRow lam i - youngRow mu i) = 2 :=
    sum_row_diff_of_twoBoxSubdiagram
      (lam := lam) (mu := mu) (by omega) hsub
  omega

theorem positiveDiffRows_nonempty_of_horizontalTwoStripChild {n : Nat}
    {lam : YoungDiagram ((n + 1) + 1)} {mu : YoungDiagram n}
    (h : IsHorizontalTwoStripChild lam mu) :
    (positiveDiffRows lam mu).Nonempty :=
  positiveDiffRows_nonempty_of_twoBoxSubdiagram h.2.1

theorem positiveDiffRows_nonempty_of_verticalTwoStripChild {n : Nat}
    {lam : YoungDiagram ((n + 1) + 1)} {mu : YoungDiagram n}
    (h : IsVerticalTwoStripChild lam mu) :
    (positiveDiffRows lam mu).Nonempty :=
  positiveDiffRows_nonempty_of_twoBoxSubdiagram h.2.1

noncomputable def minPositiveDiffRowOfHorizontal {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1))
    (x : {mu : YoungDiagram n // mu ∈ horizontalTwoStripChildrenSized lam}) :
    Nat :=
  (positiveDiffRows lam x.1).min'
    (positiveDiffRows_nonempty_of_horizontalTwoStripChild
      ((mem_horizontalTwoStripChildrenSized_iff lam x.1).mp x.2))

noncomputable def maxPositiveDiffRowOfHorizontal {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1))
    (x : {mu : YoungDiagram n // mu ∈ horizontalTwoStripChildrenSized lam}) :
    Nat :=
  (positiveDiffRows lam x.1).max'
    (positiveDiffRows_nonempty_of_horizontalTwoStripChild
      ((mem_horizontalTwoStripChildrenSized_iff lam x.1).mp x.2))

noncomputable def minPositiveDiffRowOfVertical {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1))
    (x : {mu : YoungDiagram n // mu ∈ verticalTwoStripChildrenSized lam}) :
    Nat :=
  (positiveDiffRows lam x.1).min'
    (positiveDiffRows_nonempty_of_verticalTwoStripChild
      ((mem_verticalTwoStripChildrenSized_iff lam x.1).mp x.2))

noncomputable def maxPositiveDiffRowOfVertical {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1))
    (x : {mu : YoungDiagram n // mu ∈ verticalTwoStripChildrenSized lam}) :
    Nat :=
  (positiveDiffRows lam x.1).max'
    (positiveDiffRows_nonempty_of_verticalTwoStripChild
      ((mem_verticalTwoStripChildrenSized_iff lam x.1).mp x.2))

theorem minPositiveDiffRowOfHorizontal_mem {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1))
    (x : {mu : YoungDiagram n // mu ∈ horizontalTwoStripChildrenSized lam}) :
    minPositiveDiffRowOfHorizontal lam x ∈ positiveDiffRows lam x.1 := by
  unfold minPositiveDiffRowOfHorizontal
  exact Finset.min'_mem _ _

theorem maxPositiveDiffRowOfHorizontal_mem {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1))
    (x : {mu : YoungDiagram n // mu ∈ horizontalTwoStripChildrenSized lam}) :
    maxPositiveDiffRowOfHorizontal lam x ∈ positiveDiffRows lam x.1 := by
  unfold maxPositiveDiffRowOfHorizontal
  exact Finset.max'_mem _ _

theorem minPositiveDiffRowOfVertical_mem {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1))
    (x : {mu : YoungDiagram n // mu ∈ verticalTwoStripChildrenSized lam}) :
    minPositiveDiffRowOfVertical lam x ∈ positiveDiffRows lam x.1 := by
  unfold minPositiveDiffRowOfVertical
  exact Finset.min'_mem _ _

theorem maxPositiveDiffRowOfVertical_mem {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1))
    (x : {mu : YoungDiagram n // mu ∈ verticalTwoStripChildrenSized lam}) :
    maxPositiveDiffRowOfVertical lam x ∈ positiveDiffRows lam x.1 := by
  unfold maxPositiveDiffRowOfVertical
  exact Finset.max'_mem _ _

theorem minPositiveDiffRowOfHorizontal_lt {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1))
    (x : {mu : YoungDiagram n // mu ∈ horizontalTwoStripChildrenSized lam}) :
    minPositiveDiffRowOfHorizontal lam x < (n + 1) + 1 :=
  ((mem_positiveDiffRows_iff lam x.1 _).mp
    (minPositiveDiffRowOfHorizontal_mem lam x)).1

theorem maxPositiveDiffRowOfHorizontal_lt {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1))
    (x : {mu : YoungDiagram n // mu ∈ horizontalTwoStripChildrenSized lam}) :
    maxPositiveDiffRowOfHorizontal lam x < (n + 1) + 1 :=
  ((mem_positiveDiffRows_iff lam x.1 _).mp
    (maxPositiveDiffRowOfHorizontal_mem lam x)).1

theorem minPositiveDiffRowOfVertical_lt {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1))
    (x : {mu : YoungDiagram n // mu ∈ verticalTwoStripChildrenSized lam}) :
    minPositiveDiffRowOfVertical lam x < (n + 1) + 1 :=
  ((mem_positiveDiffRows_iff lam x.1 _).mp
    (minPositiveDiffRowOfVertical_mem lam x)).1

theorem maxPositiveDiffRowOfVertical_lt {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1))
    (x : {mu : YoungDiagram n // mu ∈ verticalTwoStripChildrenSized lam}) :
    maxPositiveDiffRowOfVertical lam x < (n + 1) + 1 :=
  ((mem_positiveDiffRows_iff lam x.1 _).mp
    (maxPositiveDiffRowOfVertical_mem lam x)).1

theorem twoStripRowDiff_minPositiveDiffRowOfHorizontal_pos {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1))
    (x : {mu : YoungDiagram n // mu ∈ horizontalTwoStripChildrenSized lam}) :
    0 < twoStripRowDiff lam x.1 (minPositiveDiffRowOfHorizontal lam x) :=
  ((mem_positiveDiffRows_iff lam x.1 _).mp
    (minPositiveDiffRowOfHorizontal_mem lam x)).2

theorem twoStripRowDiff_maxPositiveDiffRowOfHorizontal_pos {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1))
    (x : {mu : YoungDiagram n // mu ∈ horizontalTwoStripChildrenSized lam}) :
    0 < twoStripRowDiff lam x.1 (maxPositiveDiffRowOfHorizontal lam x) :=
  ((mem_positiveDiffRows_iff lam x.1 _).mp
    (maxPositiveDiffRowOfHorizontal_mem lam x)).2

theorem twoStripRowDiff_minPositiveDiffRowOfVertical_pos {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1))
    (x : {mu : YoungDiagram n // mu ∈ verticalTwoStripChildrenSized lam}) :
    0 < twoStripRowDiff lam x.1 (minPositiveDiffRowOfVertical lam x) :=
  ((mem_positiveDiffRows_iff lam x.1 _).mp
    (minPositiveDiffRowOfVertical_mem lam x)).2

theorem twoStripRowDiff_maxPositiveDiffRowOfVertical_pos {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1))
    (x : {mu : YoungDiagram n // mu ∈ verticalTwoStripChildrenSized lam}) :
    0 < twoStripRowDiff lam x.1 (maxPositiveDiffRowOfVertical lam x) :=
  ((mem_positiveDiffRows_iff lam x.1 _).mp
    (maxPositiveDiffRowOfVertical_mem lam x)).2

theorem isRemovableRow_of_horizontalTwoStripChild_positiveDiff {n : Nat}
    {lam : YoungDiagram ((n + 1) + 1)} {mu : YoungDiagram n}
    (h : IsHorizontalTwoStripChild lam mu) {r : Nat}
    (hpos : 0 < twoStripRowDiff lam mu r) :
    IsRemovableRow lam r := by
  unfold IsRemovableRow
  unfold twoStripRowDiff at hpos
  have hnext := next_parent_row_le_child_row_of_horizontalTwoStripChild h r
  have hrow_le := row_le_parent_of_horizontalTwoStripChild h r
  omega

theorem isRemovableRow_minPositiveDiffRowOfHorizontal {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1))
    (x : {mu : YoungDiagram n // mu ∈ horizontalTwoStripChildrenSized lam}) :
    IsRemovableRow lam (minPositiveDiffRowOfHorizontal lam x) :=
  isRemovableRow_of_horizontalTwoStripChild_positiveDiff
    ((mem_horizontalTwoStripChildrenSized_iff lam x.1).mp x.2)
    (twoStripRowDiff_minPositiveDiffRowOfHorizontal_pos lam x)

theorem positiveDiffRows_not_mem_above_max_of_vertical {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1))
    (x : {mu : YoungDiagram n // mu ∈ verticalTwoStripChildrenSized lam})
    {i : Nat} (hi : maxPositiveDiffRowOfVertical lam x < i) :
    i ∉ positiveDiffRows lam x.1 := by
  intro hmem
  have hle := (positiveDiffRows lam x.1).le_max' i hmem
  unfold maxPositiveDiffRowOfVertical at hi
  omega

theorem isRemovableRow_maxPositiveDiffRowOfVertical {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1))
    (x : {mu : YoungDiagram n // mu ∈ verticalTwoStripChildrenSized lam}) :
    IsRemovableRow lam (maxPositiveDiffRowOfVertical lam x) := by
  let r := maxPositiveDiffRowOfVertical lam x
  have hchild : IsVerticalTwoStripChild lam x.1 :=
    (mem_verticalTwoStripChildrenSized_iff lam x.1).mp x.2
  have hpos : 0 < twoStripRowDiff lam x.1 r := by
    simpa [r] using twoStripRowDiff_maxPositiveDiffRowOfVertical_pos lam x
  have hrow_le : youngRow x.1 r <= youngRow lam r :=
    row_le_parent_of_verticalTwoStripChild hchild r
  unfold IsRemovableRow
  change youngRow lam (r + 1) < youngRow lam r
  by_cases hsucc : r + 1 < (n + 1) + 1
  · have hnotmem :
        r + 1 ∉ positiveDiffRows lam x.1 :=
      positiveDiffRows_not_mem_above_max_of_vertical lam x (by
        change r < r + 1
        omega)
    have hnotpos : ¬ 0 < twoStripRowDiff lam x.1 (r + 1) := by
      intro hpos_succ
      exact hnotmem ((mem_positiveDiffRows_iff lam x.1 (r + 1)).mpr
        ⟨hsucc, hpos_succ⟩)
    have hrow_succ_le : youngRow x.1 (r + 1) <= youngRow lam (r + 1) :=
      row_le_parent_of_verticalTwoStripChild hchild (r + 1)
    have hmu_succ_le : youngRow x.1 (r + 1) <= youngRow x.1 r :=
      youngRow_succ_le x.1 r
    have hdiff_succ_zero :
        twoStripRowDiff lam x.1 (r + 1) = 0 :=
      Nat.eq_zero_of_not_pos hnotpos
    unfold twoStripRowDiff at hpos hdiff_succ_zero
    omega
  · have hlam_succ_zero : youngRow lam (r + 1) = 0 := by
      simp [youngRow, hsucc]
    unfold twoStripRowDiff at hpos
    rw [hlam_succ_zero]
    omega

noncomputable def firstRemovableRowOfHorizontalTaggedChild {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1))
    (x : {mu : YoungDiagram n // mu ∈ horizontalTwoStripChildrenSized lam}) :
    RemovableRow lam :=
  ⟨minPositiveDiffRowOfHorizontal lam x,
    isRemovableRow_minPositiveDiffRowOfHorizontal lam x⟩

noncomputable def firstRemovableRowOfVerticalTaggedChild {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1))
    (x : {mu : YoungDiagram n // mu ∈ verticalTwoStripChildrenSized lam}) :
    RemovableRow lam :=
  ⟨maxPositiveDiffRowOfVertical lam x,
    isRemovableRow_maxPositiveDiffRowOfVertical lam x⟩

theorem isOneBoxChild_deleteRemovableRow_of_positiveDiff {n : Nat}
    {lam : YoungDiagram ((n + 1) + 1)} {mu : YoungDiagram n}
    (hsub : IsYoungSubdiagram mu lam) {r : Nat}
    (hr : IsRemovableRow lam r)
    (hpos : 0 < twoStripRowDiff lam mu r) :
    IsOneBoxChild (deleteRemovableRowDiagram lam r hr) mu := by
  refine ⟨rfl, ?_⟩
  intro i
  rw [youngRow_deleteRemovableRowDiagram lam hr i]
  have hle_parent : youngRow mu (i : Nat) <= youngRow lam (i : Nat) := by
    have hi : (i : Nat) < (n + 1) + 1 := by
      exact Nat.lt_succ_of_lt i.isLt
    exact hsub ⟨i, hi⟩
  by_cases hir : (i : Nat) = r
  · subst r
    rw [if_pos rfl]
    unfold twoStripRowDiff at hpos
    omega
  · rw [if_neg hir]
    exact hle_parent

theorem horizontalTaggedChild_after_firstDeletion_mem_oneBoxChildrenSized
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (x : {mu : YoungDiagram n // mu ∈ horizontalTwoStripChildrenSized lam}) :
    x.1 ∈ oneBoxChildrenSized
      (deleteRemovableRowDiagram lam
        (firstRemovableRowOfHorizontalTaggedChild lam x).1
        (firstRemovableRowOfHorizontalTaggedChild lam x).2) := by
  exact (mem_oneBoxChildrenSized_iff _ x.1).mpr
    (isOneBoxChild_deleteRemovableRow_of_positiveDiff
      (((mem_horizontalTwoStripChildrenSized_iff lam x.1).mp x.2).2.1)
      (firstRemovableRowOfHorizontalTaggedChild lam x).2
      (twoStripRowDiff_minPositiveDiffRowOfHorizontal_pos lam x))

theorem verticalTaggedChild_after_firstDeletion_mem_oneBoxChildrenSized
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (x : {mu : YoungDiagram n // mu ∈ verticalTwoStripChildrenSized lam}) :
    x.1 ∈ oneBoxChildrenSized
      (deleteRemovableRowDiagram lam
        (firstRemovableRowOfVerticalTaggedChild lam x).1
        (firstRemovableRowOfVerticalTaggedChild lam x).2) := by
  exact (mem_oneBoxChildrenSized_iff _ x.1).mpr
    (isOneBoxChild_deleteRemovableRow_of_positiveDiff
      (((mem_verticalTwoStripChildrenSized_iff lam x.1).mp x.2).2.1)
      (firstRemovableRowOfVerticalTaggedChild lam x).2
      (twoStripRowDiff_maxPositiveDiffRowOfVertical_pos lam x))

noncomputable instance removableRowFintype {n : Nat}
    (lam : YoungDiagram (n + 1)) : Fintype (RemovableRow lam) := by
  classical
  exact Fintype.ofInjective
    (fun r : RemovableRow lam => (⟨r.1, removableRow_lt_size r.2⟩ : Fin (n + 1)))
    (by
      intro r s h
      apply Subtype.ext
      exact congrArg Fin.val h)

def removableRowToOneBoxChild {n : Nat} (lam : YoungDiagram (n + 1))
    (r : RemovableRow lam) : YoungDiagram n :=
  deleteRemovableRowDiagram lam r.1 r.2

theorem removableRowToOneBoxChild_isOneBoxChild {n : Nat}
    (lam : YoungDiagram (n + 1)) (r : RemovableRow lam) :
    IsOneBoxChild lam (removableRowToOneBoxChild lam r) := by
  exact deleteRemovableRowDiagram_isOneBoxChild lam r.2

theorem removableRowToOneBoxChild_mem {n : Nat}
    (lam : YoungDiagram (n + 1)) (r : RemovableRow lam) :
    removableRowToOneBoxChild lam r ∈ oneBoxChildren lam := by
  classical
  rw [oneBoxChildren]
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, removableRowToOneBoxChild_isOneBoxChild lam r⟩

theorem removableRowToOneBoxChild_mem_sized {n : Nat}
    (lam : YoungDiagram (n + 1)) (r : RemovableRow lam) :
    removableRowToOneBoxChild lam r ∈ oneBoxChildrenSized lam := by
  classical
  rw [oneBoxChildrenSized]
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, removableRowToOneBoxChild_isOneBoxChild lam r⟩

noncomputable def oneBoxChildToRemovableRow {n : Nat}
    (lam : YoungDiagram (n + 1))
    (mu : {mu : YoungDiagram n // mu ∈ oneBoxChildren lam}) :
    RemovableRow lam := by
  classical
  have hchild : IsOneBoxChild lam mu.1 := by
    simpa [oneBoxChildren] using (Finset.mem_filter.mp mu.2).2
  let hrow := exists_removableRow_of_oneBoxChild hchild
  exact ⟨Classical.choose hrow, (Classical.choose_spec hrow).1⟩

theorem oneBoxChildToRemovableRow_row_form {n : Nat}
    (lam : YoungDiagram (n + 1))
    (mu : {mu : YoungDiagram n // mu ∈ oneBoxChildren lam}) :
    youngRow lam (oneBoxChildToRemovableRow lam mu).1 =
        youngRow mu.1 (oneBoxChildToRemovableRow lam mu).1 + 1 ∧
      forall s : Nat, s ≠ (oneBoxChildToRemovableRow lam mu).1 ->
        youngRow lam s = youngRow mu.1 s := by
  classical
  unfold oneBoxChildToRemovableRow
  dsimp
  let hchild : IsOneBoxChild lam mu.1 := by
    simpa [oneBoxChildren] using (Finset.mem_filter.mp mu.2).2
  let hrow := exists_removableRow_of_oneBoxChild hchild
  exact (Classical.choose_spec hrow).2

noncomputable def oneBoxChildToRemovableRowSized {n : Nat}
    (lam : YoungDiagram (n + 1))
    (mu : {mu : YoungDiagram n // mu ∈ oneBoxChildrenSized lam}) :
    RemovableRow lam := by
  classical
  have hchild : IsOneBoxChild lam mu.1 := by
    simpa [oneBoxChildrenSized] using (Finset.mem_filter.mp mu.2).2
  let hrow := exists_removableRow_of_oneBoxChild hchild
  exact ⟨Classical.choose hrow, (Classical.choose_spec hrow).1⟩

theorem oneBoxChildToRemovableRowSized_row_form {n : Nat}
    (lam : YoungDiagram (n + 1))
    (mu : {mu : YoungDiagram n // mu ∈ oneBoxChildrenSized lam}) :
    youngRow lam (oneBoxChildToRemovableRowSized lam mu).1 =
        youngRow mu.1 (oneBoxChildToRemovableRowSized lam mu).1 + 1 ∧
      forall s : Nat, s ≠ (oneBoxChildToRemovableRowSized lam mu).1 ->
        youngRow lam s = youngRow mu.1 s := by
  classical
  unfold oneBoxChildToRemovableRowSized
  dsimp
  let hchild : IsOneBoxChild lam mu.1 := by
    simpa [oneBoxChildrenSized] using (Finset.mem_filter.mp mu.2).2
  let hrow := exists_removableRow_of_oneBoxChild hchild
  exact (Classical.choose_spec hrow).2

theorem oneBoxChildToRemovableRowSized_removableRowToOneBoxChild {n : Nat}
    (lam : YoungDiagram (n + 1)) (r : RemovableRow lam) :
    oneBoxChildToRemovableRowSized lam
        ⟨removableRowToOneBoxChild lam r,
          removableRowToOneBoxChild_mem_sized lam r⟩ = r := by
  apply Subtype.ext
  let mu : {mu : YoungDiagram n // mu ∈ oneBoxChildrenSized lam} :=
    ⟨removableRowToOneBoxChild lam r,
      removableRowToOneBoxChild_mem_sized lam r⟩
  have hchosen := oneBoxChildToRemovableRowSized_row_form lam mu
  have hconstructed := row_form_deleteRemovableRowDiagram lam r.2
  rcases existsUnique_row_of_oneBoxChild
      (removableRowToOneBoxChild_isOneBoxChild lam r) with
    ⟨u, _hu, huniq⟩
  have hchosen_eq :
      (oneBoxChildToRemovableRowSized lam mu).1 = u := huniq _ hchosen
  have hconstructed_eq : r.1 = u := huniq _ hconstructed
  exact hchosen_eq.trans hconstructed_eq.symm

theorem removableRowToOneBoxChild_oneBoxChildToRemovableRowSized {n : Nat}
    (lam : YoungDiagram (n + 1))
    (mu : {mu : YoungDiagram n // mu ∈ oneBoxChildrenSized lam}) :
    removableRowToOneBoxChild lam (oneBoxChildToRemovableRowSized lam mu) =
      mu.1 := by
  let r := oneBoxChildToRemovableRowSized lam mu
  change deleteRemovableRowDiagram lam r.1 r.2 = mu.1
  have hmu := oneBoxChildToRemovableRowSized_row_form lam mu
  change youngRow lam r.1 = youngRow mu.1 r.1 + 1 ∧
      (∀ s : Nat, s ≠ r.1 -> youngRow lam s = youngRow mu.1 s) at hmu
  have hconstructed := row_form_deleteRemovableRowDiagram lam r.2
  apply youngDiagram_ext_youngRow
  intro i
  by_cases hir : i = r.1
  · subst i
    have hmu_at := hmu.1
    have hconstructed_at := hconstructed.1
    omega
  · have hmu_other := hmu.2 i hir
    have hconstructed_other := hconstructed.2 i hir
    rw [← hconstructed_other, ← hmu_other]

noncomputable def removableRowsEquivOneBoxChildren {n : Nat}
    (lam : YoungDiagram (n + 1)) :
    RemovableRow lam ≃ {mu : YoungDiagram n // mu ∈ oneBoxChildrenSized lam} where
  toFun r :=
    ⟨removableRowToOneBoxChild lam r, removableRowToOneBoxChild_mem_sized lam r⟩
  invFun mu := oneBoxChildToRemovableRowSized lam mu
  left_inv r := oneBoxChildToRemovableRowSized_removableRowToOneBoxChild lam r
  right_inv mu := by
    apply Subtype.ext
    exact removableRowToOneBoxChild_oneBoxChildToRemovableRowSized lam mu

theorem isRemovableRow_of_removableCornerBox {n : Nat}
    {lam : YoungDiagram n} {u : Nat × Nat}
    (h : IsRemovableCornerBox lam u) :
    IsRemovableRow lam u.1 := by
  unfold IsRemovableCornerBox IsYoungBox IsRemovableRow at *
  omega

noncomputable def maxRemovableCornerCell {n : Nat}
    {lam : YoungDiagram (n + 1)} (T : StandardYoungTableau lam) :
    YoungCell lam :=
  Classical.choose (ExistsUnique.exists
    (existsUnique_removableCornerBox_tableauMaxAt T))

theorem maxRemovableCornerCell_spec {n : Nat}
    {lam : YoungDiagram (n + 1)} (T : StandardYoungTableau lam) :
    TableauMaxAt T (maxRemovableCornerCell T) ∧
      IsRemovableCornerBox lam
        (YoungCell.toNatPair (maxRemovableCornerCell T)) := by
  unfold maxRemovableCornerCell
  exact Classical.choose_spec (ExistsUnique.exists
    (existsUnique_removableCornerBox_tableauMaxAt T))

noncomputable def maxRemovableRow {n : Nat}
    {lam : YoungDiagram (n + 1)} (T : StandardYoungTableau lam) :
    RemovableRow lam :=
  ⟨YoungCell.row (maxRemovableCornerCell T),
    isRemovableRow_of_removableCornerBox
      (maxRemovableCornerCell_spec T).2⟩

theorem tableauMaxAt_maxRemovableCornerCell {n : Nat}
    {lam : YoungDiagram (n + 1)} (T : StandardYoungTableau lam) :
    TableauMaxAt T (maxRemovableCornerCell T) := by
  exact (maxRemovableCornerCell_spec T).1

theorem maxRemovableRow_isRemovable {n : Nat}
    {lam : YoungDiagram (n + 1)} (T : StandardYoungTableau lam) :
    IsRemovableRow lam (maxRemovableRow T).1 :=
  (maxRemovableRow T).2

theorem tableauMaxAt_deletedCorner_maxRemovableRow {n : Nat}
    {lam : YoungDiagram (n + 1)} (T : StandardYoungTableau lam) :
    TableauMaxAt T
      (deletedCornerCellOfOneBoxChildRow
        (deleteRemovableRowDiagram_isOneBoxChild lam (maxRemovableRow T).2)
        (row_form_deleteRemovableRowDiagram lam (maxRemovableRow T).2)) := by
  let u := maxRemovableCornerCell T
  let r : RemovableRow lam := maxRemovableRow T
  have hcorner :
      IsRemovableCornerBox lam (YoungCell.toNatPair u) :=
    (maxRemovableCornerCell_spec T).2
  have hcol_u : YoungCell.col u = youngRow lam r.1 - 1 := by
    unfold IsRemovableCornerBox IsYoungBox YoungCell.toNatPair at hcorner
    rcases hcorner with ⟨_hbox, hlast, _hbelow⟩
    change YoungCell.col u + 1 = youngRow lam (YoungCell.row u) at hlast
    have hrow_u : YoungCell.row u = r.1 := by
      simp [r, maxRemovableRow, u]
    rw [hrow_u] at hlast
    omega
  have hchild_row :
      youngRow (deleteRemovableRowDiagram lam r.1 r.2) r.1 =
        youngRow lam r.1 - 1 := by
    rw [youngRow_deleteRemovableRowDiagram lam r.2 r.1]
    simp
  have hcell :
      deletedCornerCellOfOneBoxChildRow
          (deleteRemovableRowDiagram_isOneBoxChild lam r.2)
          (row_form_deleteRemovableRowDiagram lam r.2)
        = u := by
    apply YoungCell.ext_row_col
    · rw [deletedCornerCell_row]
      simp [r, maxRemovableRow, u]
    · rw [deletedCornerCell_col]
      rw [hchild_row, hcol_u]
  change TableauMaxAt T
      (deletedCornerCellOfOneBoxChildRow
        (deleteRemovableRowDiagram_isOneBoxChild lam r.2)
        (row_form_deleteRemovableRowDiagram lam r.2))
  rw [hcell]
  exact tableauMaxAt_maxRemovableCornerCell T

theorem deletedCornerCell_removableCornerBox_of_removableRow {n : Nat}
    {lam : YoungDiagram (n + 1)} (r : RemovableRow lam) :
    IsRemovableCornerBox lam
      (YoungCell.toNatPair
        (deletedCornerCellOfOneBoxChildRow
          (deleteRemovableRowDiagram_isOneBoxChild lam r.2)
          (row_form_deleteRemovableRowDiagram lam r.2))) := by
  let u :=
    deletedCornerCellOfOneBoxChildRow
      (deleteRemovableRowDiagram_isOneBoxChild lam r.2)
      (row_form_deleteRemovableRowDiagram lam r.2)
  have hrow :
      YoungCell.row u = r.1 := by
    dsimp [u]
    exact deletedCornerCell_row
      (deleteRemovableRowDiagram_isOneBoxChild lam r.2)
      (row_form_deleteRemovableRowDiagram lam r.2)
  have hchild_row :
      youngRow (deleteRemovableRowDiagram lam r.1 r.2) r.1 =
        youngRow lam r.1 - 1 := by
    rw [youngRow_deleteRemovableRowDiagram lam r.2 r.1]
    simp
  have hcol :
      YoungCell.col u = youngRow lam r.1 - 1 := by
    dsimp [u]
    rw [deletedCornerCell_col
      (deleteRemovableRowDiagram_isOneBoxChild lam r.2)
      (row_form_deleteRemovableRowDiagram lam r.2)]
    exact hchild_row
  change IsRemovableCornerBox lam (YoungCell.row u, YoungCell.col u)
  rw [hrow, hcol]
  exact removableCornerBox_of_removableRow (lam := lam) r.2

theorem maxRemovableRow_eq_of_tableauMaxAt_deletedCorner {n : Nat}
    {lam : YoungDiagram (n + 1)} (r : RemovableRow lam)
    (T : StandardYoungTableau lam)
    (hT :
      TableauMaxAt T
        (deletedCornerCellOfOneBoxChildRow
          (deleteRemovableRowDiagram_isOneBoxChild lam r.2)
          (row_form_deleteRemovableRowDiagram lam r.2))) :
    maxRemovableRow T = r := by
  let u :=
    deletedCornerCellOfOneBoxChildRow
      (deleteRemovableRowDiagram_isOneBoxChild lam r.2)
      (row_form_deleteRemovableRowDiagram lam r.2)
  rcases existsUnique_removableCornerBox_tableauMaxAt T with
    ⟨u₀, hu₀, huniq⟩
  have hu : u = u₀ := huniq u
    ⟨hT, deletedCornerCell_removableCornerBox_of_removableRow r⟩
  have hmax : maxRemovableCornerCell T = u₀ :=
    huniq (maxRemovableCornerCell T) (maxRemovableCornerCell_spec T)
  have hcell : u = maxRemovableCornerCell T := hu.trans hmax.symm
  apply Subtype.ext
  change YoungCell.row (maxRemovableCornerCell T) = r.1
  rw [← hcell]
  exact deletedCornerCell_row
    (deleteRemovableRowDiagram_isOneBoxChild lam r.2)
    (row_form_deleteRemovableRowDiagram lam r.2)

noncomputable instance maxRemovableRowFiberFintype {n : Nat}
    {lam : YoungDiagram (n + 1)} (r : RemovableRow lam) :
    Fintype {T : StandardYoungTableau lam // maxRemovableRow T = r} := by
  classical
  infer_instance

noncomputable def maxRemovableRowFiberEquivDeletedCorner {n : Nat}
    {lam : YoungDiagram (n + 1)} (r : RemovableRow lam) :
    {T : StandardYoungTableau lam // maxRemovableRow T = r} ≃
      {T : StandardYoungTableau lam //
        TableauMaxAt T
          (deletedCornerCellOfOneBoxChildRow
            (deleteRemovableRowDiagram_isOneBoxChild lam r.2)
            (row_form_deleteRemovableRowDiagram lam r.2))} :=
  Equiv.subtypeEquivRight (fun T => by
    constructor
    · intro hT
      cases hT
      exact tableauMaxAt_deletedCorner_maxRemovableRow T
    · intro hT
      exact maxRemovableRow_eq_of_tableauMaxAt_deletedCorner r T hT)

theorem card_maxRemovableRow_fiber_eq_deletedCorner {n : Nat}
    {lam : YoungDiagram (n + 1)} (r : RemovableRow lam) :
    Fintype.card {T : StandardYoungTableau lam // maxRemovableRow T = r} =
      Fintype.card
        {T : StandardYoungTableau lam //
          TableauMaxAt T
            (deletedCornerCellOfOneBoxChildRow
              (deleteRemovableRowDiagram_isOneBoxChild lam r.2)
              (row_form_deleteRemovableRowDiagram lam r.2))} := by
  classical
  exact Fintype.card_congr (maxRemovableRowFiberEquivDeletedCorner r)

theorem card_maxRemovableRow_fiber_eq_child {n : Nat}
    {lam : YoungDiagram (n + 1)} (r : RemovableRow lam) :
    Fintype.card {T : StandardYoungTableau lam // maxRemovableRow T = r} =
      Fintype.card (StandardYoungTableau (removableRowToOneBoxChild lam r)) := by
  rw [card_maxRemovableRow_fiber_eq_deletedCorner r]
  exact card_tableaux_maxAt_deletedCorner_eq_child
    (deleteRemovableRowDiagram_isOneBoxChild lam r.2)
    (row_form_deleteRemovableRowDiagram lam r.2)

noncomputable def standardYoungTableauEquivSigmaMaxRemovableRow {n : Nat}
    (lam : YoungDiagram (n + 1)) :
    StandardYoungTableau lam ≃
      Sigma (fun r : RemovableRow lam =>
        {T : StandardYoungTableau lam // maxRemovableRow T = r}) where
  toFun T := ⟨maxRemovableRow T, ⟨T, rfl⟩⟩
  invFun x := x.2.1
  left_inv T := rfl
  right_inv x := by
    rcases x with ⟨r, T, hT⟩
    cases hT
    rfl

theorem card_standardYoungTableau_eq_sum_maxRemovableRow_fibers {n : Nat}
    (lam : YoungDiagram (n + 1)) :
    Fintype.card (StandardYoungTableau lam) =
      ∑ r : RemovableRow lam,
        Fintype.card {T : StandardYoungTableau lam // maxRemovableRow T = r} := by
  classical
  rw [Fintype.card_congr
    (standardYoungTableauEquivSigmaMaxRemovableRow lam)]
  exact Fintype.card_sigma

theorem card_standardYoungTableau_eq_sum_removableRow_children {n : Nat}
    (lam : YoungDiagram (n + 1)) :
    Fintype.card (StandardYoungTableau lam) =
      ∑ r : RemovableRow lam,
        Fintype.card (StandardYoungTableau (removableRowToOneBoxChild lam r)) := by
  rw [card_standardYoungTableau_eq_sum_maxRemovableRow_fibers lam]
  exact Finset.sum_congr rfl (fun r _ =>
    card_maxRemovableRow_fiber_eq_child r)

theorem tableauDim_eq_sum_removableRow_children {n : Nat}
    (lam : YoungDiagram (n + 1)) :
    tableauDim lam =
      ∑ r : RemovableRow lam, tableauDim (removableRowToOneBoxChild lam r) := by
  have hnat := card_standardYoungTableau_eq_sum_removableRow_children lam
  change ((Fintype.card (StandardYoungTableau lam) : Nat) : ℝ) =
    ∑ r : RemovableRow lam,
      ((Fintype.card
        (StandardYoungTableau (removableRowToOneBoxChild lam r)) : Nat) : ℝ)
  rw [← Nat.cast_sum, hnat]

theorem sum_removableRows_tableauDim_eq_oneBoxChildrenSized {n : Nat}
    (lam : YoungDiagram (n + 1)) :
    (∑ r : RemovableRow lam, tableauDim (removableRowToOneBoxChild lam r)) =
      (oneBoxChildrenSized lam).sum (fun mu => tableauDim mu) := by
  classical
  have hsum_subtype :
      (∑ mu : {mu : YoungDiagram n // mu ∈ oneBoxChildrenSized lam},
        tableauDim mu.1) =
        (oneBoxChildrenSized lam).sum (fun mu => tableauDim mu) := by
    rw [Finset.univ_eq_attach]
    exact Finset.sum_attach (oneBoxChildrenSized lam) (fun mu => tableauDim mu)
  exact (Fintype.sum_equiv
    (removableRowsEquivOneBoxChildren lam)
    (fun r : RemovableRow lam => tableauDim (removableRowToOneBoxChild lam r))
    (fun mu : {mu : YoungDiagram n // mu ∈ oneBoxChildrenSized lam} =>
      tableauDim mu.1)
    (fun _ => rfl)).trans hsum_subtype

theorem tableauDim_oneBox_branching_sized {n : Nat}
    (lam : YoungDiagram (n + 1)) :
    tableauDim lam = (oneBoxChildrenSized lam).sum (fun mu => tableauDim mu) := by
  rw [tableauDim_eq_sum_removableRow_children lam]
  exact sum_removableRows_tableauDim_eq_oneBoxChildrenSized lam

theorem oneBoxChildrenSized_eq_oneBoxChildrenOdd (m : Nat)
    (lam : YoungDiagram (2 * m + 1)) :
    oneBoxChildrenSized lam = oneBoxChildrenOdd m lam := by
  ext mu
  simp [oneBoxChildrenSized, oneBoxChildrenOdd]

theorem tableauDim_oneBoxChildrenOdd_branching (m : Nat)
    (lam : YoungDiagram (2 * m + 1)) :
    tableauDim lam =
      (oneBoxChildrenOdd m lam).sum (fun mu => tableauDim mu) := by
  rw [← oneBoxChildrenSized_eq_oneBoxChildrenOdd m lam]
  exact tableauDim_oneBox_branching_sized lam

theorem youngRow_deleteRemovableRowDiagram_le_parent {n : Nat}
    (lam : YoungDiagram (n + 1)) {r : Nat} (hr : IsRemovableRow lam r)
    (i : Nat) :
    youngRow (deleteRemovableRowDiagram lam r hr) i <= youngRow lam i := by
  rw [youngRow_deleteRemovableRowDiagram lam hr i]
  by_cases hir : i = r <;> simp [hir]

/-- Two successive removable-row deletions from a diagram. -/
structure TwoStepRemovableRows {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) where
  first : RemovableRow lam
  second : RemovableRow (deleteRemovableRowDiagram lam first.1 first.2)

def twoStepRemovableRowsEquivSigma {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) :
    TwoStepRemovableRows lam ≃
      Sigma (fun r : RemovableRow lam =>
        RemovableRow (removableRowToOneBoxChild lam r)) where
  toFun p := ⟨p.first, p.second⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv p := by
    cases p
    rfl
  right_inv x := by
    cases x
    rfl

noncomputable instance twoStepRemovableRowsFintype {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) :
    Fintype (TwoStepRemovableRows lam) := by
  classical
  exact Fintype.ofEquiv
    (Sigma (fun r : RemovableRow lam =>
      RemovableRow (removableRowToOneBoxChild lam r)))
    (twoStepRemovableRowsEquivSigma lam).symm

/-- Delete two boxes by deleting a removable row, then deleting a removable row
of the intermediate child. -/
def deleteTwoRemovableRowsDiagram {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (p : TwoStepRemovableRows lam) :
    YoungDiagram n :=
  deleteRemovableRowDiagram
    (deleteRemovableRowDiagram lam p.first.1 p.first.2)
    p.second.1 p.second.2

theorem youngRow_deleteTwoRemovableRowsDiagram {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (p : TwoStepRemovableRows lam)
    (i : Nat) :
    youngRow (deleteTwoRemovableRowsDiagram lam p) i =
      if i = p.second.1 then
        youngRow (deleteRemovableRowDiagram lam p.first.1 p.first.2)
          p.second.1 - 1
      else
        youngRow (deleteRemovableRowDiagram lam p.first.1 p.first.2) i := by
  exact youngRow_deleteRemovableRowDiagram
    (deleteRemovableRowDiagram lam p.first.1 p.first.2) p.second.2 i

theorem deleteTwoRemovableRows_isYoungSubdiagram {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (p : TwoStepRemovableRows lam) :
    IsYoungSubdiagram (deleteTwoRemovableRowsDiagram lam p) lam := by
  intro i
  calc
    youngRow (deleteTwoRemovableRowsDiagram lam p) i
        <= youngRow (deleteRemovableRowDiagram lam p.first.1 p.first.2) i :=
      youngRow_deleteRemovableRowDiagram_le_parent
        (deleteRemovableRowDiagram lam p.first.1 p.first.2) p.second.2 i
    _ <= youngRow lam i :=
      youngRow_deleteRemovableRowDiagram_le_parent lam p.first.2 i

theorem sum_row_diff_deleteTwoRemovableRows {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (p : TwoStepRemovableRows lam) :
    (Finset.range ((n + 1) + 1)).sum
        (fun i => youngRow lam i -
          youngRow (deleteTwoRemovableRowsDiagram lam p) i) = 2 := by
  exact sum_row_diff_of_twoBoxSubdiagram
    (lam := lam) (mu := deleteTwoRemovableRowsDiagram lam p)
    (by omega) (deleteTwoRemovableRows_isYoungSubdiagram lam p)

def twoStepFirstChild {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (p : TwoStepRemovableRows lam) :
    YoungDiagram (n + 1) :=
  deleteRemovableRowDiagram lam p.first.1 p.first.2

theorem twoStepFirstChild_isOneBoxChild {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (p : TwoStepRemovableRows lam) :
    IsOneBoxChild lam (twoStepFirstChild lam p) := by
  exact deleteRemovableRowDiagram_isOneBoxChild lam p.first.2

theorem twoStepFirstChild_row_form {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (p : TwoStepRemovableRows lam) :
    youngRow lam p.first.1 =
        youngRow (twoStepFirstChild lam p) p.first.1 + 1 ∧
      forall t : Nat, t ≠ p.first.1 ->
        youngRow lam t = youngRow (twoStepFirstChild lam p) t := by
  exact row_form_deleteRemovableRowDiagram lam p.first.2

theorem twoStepSecondChild_isOneBoxChild {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (p : TwoStepRemovableRows lam) :
    IsOneBoxChild (twoStepFirstChild lam p)
      (deleteTwoRemovableRowsDiagram lam p) := by
  exact deleteRemovableRowDiagram_isOneBoxChild
    (twoStepFirstChild lam p) p.second.2

theorem twoStepSecondChild_row_form {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (p : TwoStepRemovableRows lam) :
    youngRow (twoStepFirstChild lam p) p.second.1 =
        youngRow (deleteTwoRemovableRowsDiagram lam p) p.second.1 + 1 ∧
      forall t : Nat, t ≠ p.second.1 ->
        youngRow (twoStepFirstChild lam p) t =
          youngRow (deleteTwoRemovableRowsDiagram lam p) t := by
  exact row_form_deleteRemovableRowDiagram (twoStepFirstChild lam p) p.second.2

def firstDeletedCornerOfTwoStep {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (p : TwoStepRemovableRows lam) :
    YoungCell lam :=
  deletedCornerCellOfOneBoxChildRow
    (twoStepFirstChild_isOneBoxChild lam p)
    (twoStepFirstChild_row_form lam p)

def secondDeletedCornerOfTwoStepInChild {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (p : TwoStepRemovableRows lam) :
    YoungCell (twoStepFirstChild lam p) :=
  deletedCornerCellOfOneBoxChildRow
    (twoStepSecondChild_isOneBoxChild lam p)
    (twoStepSecondChild_row_form lam p)

def secondDeletedCornerOfTwoStepInParent {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (p : TwoStepRemovableRows lam) :
    YoungCell lam :=
  childCellToParentCellOfOneBoxChildRow
    (twoStepFirstChild_isOneBoxChild lam p)
    (twoStepFirstChild_row_form lam p)
    (secondDeletedCornerOfTwoStepInChild lam p)

theorem firstDeletedCornerOfTwoStep_row {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (p : TwoStepRemovableRows lam) :
    YoungCell.row (firstDeletedCornerOfTwoStep lam p) = p.first.1 := by
  exact deletedCornerCell_row
    (twoStepFirstChild_isOneBoxChild lam p)
    (twoStepFirstChild_row_form lam p)

theorem firstDeletedCornerOfTwoStep_col {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (p : TwoStepRemovableRows lam) :
    YoungCell.col (firstDeletedCornerOfTwoStep lam p) =
      youngRow (twoStepFirstChild lam p) p.first.1 := by
  exact deletedCornerCell_col
    (twoStepFirstChild_isOneBoxChild lam p)
    (twoStepFirstChild_row_form lam p)

theorem secondDeletedCornerOfTwoStepInChild_row {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (p : TwoStepRemovableRows lam) :
    YoungCell.row (secondDeletedCornerOfTwoStepInChild lam p) =
      p.second.1 := by
  exact deletedCornerCell_row
    (twoStepSecondChild_isOneBoxChild lam p)
    (twoStepSecondChild_row_form lam p)

theorem secondDeletedCornerOfTwoStepInChild_col {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (p : TwoStepRemovableRows lam) :
    YoungCell.col (secondDeletedCornerOfTwoStepInChild lam p) =
      youngRow (deleteTwoRemovableRowsDiagram lam p) p.second.1 := by
  exact deletedCornerCell_col
    (twoStepSecondChild_isOneBoxChild lam p)
    (twoStepSecondChild_row_form lam p)

theorem secondDeletedCornerOfTwoStepInParent_row {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (p : TwoStepRemovableRows lam) :
    YoungCell.row (secondDeletedCornerOfTwoStepInParent lam p) =
      p.second.1 := by
  rw [secondDeletedCornerOfTwoStepInParent]
  rw [childCellToParentCell_row]
  exact secondDeletedCornerOfTwoStepInChild_row lam p

theorem secondDeletedCornerOfTwoStepInParent_col {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (p : TwoStepRemovableRows lam) :
    YoungCell.col (secondDeletedCornerOfTwoStepInParent lam p) =
      youngRow (deleteTwoRemovableRowsDiagram lam p) p.second.1 := by
  rw [secondDeletedCornerOfTwoStepInParent]
  rw [childCellToParentCell_col]
  exact secondDeletedCornerOfTwoStepInChild_col lam p

theorem youngRow_deleteTwoRemovableRowsDiagram_eq_parent {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (p : TwoStepRemovableRows lam)
    (i : Nat) :
    youngRow (deleteTwoRemovableRowsDiagram lam p) i =
      if i = p.second.1 then
        (if i = p.first.1 then youngRow lam p.first.1 - 1 else youngRow lam i) - 1
      else if i = p.first.1 then youngRow lam p.first.1 - 1 else youngRow lam i := by
  rw [youngRow_deleteTwoRemovableRowsDiagram]
  by_cases hi : i = p.second.1
  · subst i
    simp [youngRow_deleteRemovableRowDiagram]
  · simp [hi, youngRow_deleteRemovableRowDiagram]

theorem deleteTwoRemovableRows_vertical_of_distinct_rows {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (p : TwoStepRemovableRows lam)
    (hrows : p.first.1 ≠ p.second.1) :
    IsVerticalTwoStripChild lam (deleteTwoRemovableRowsDiagram lam p) := by
  refine ⟨by omega, deleteTwoRemovableRows_isYoungSubdiagram lam p, ?_⟩
  intro i
  rw [youngRow_deleteTwoRemovableRowsDiagram_eq_parent]
  by_cases hi_second : (i : Nat) = p.second.1
  · have hi_first : (i : Nat) ≠ p.first.1 := by
      intro h
      exact hrows (h.symm.trans hi_second)
    have hmid_pos :
        0 < youngRow (twoStepFirstChild lam p) p.second.1 :=
      removableRow_pos p.second.2
    have hlam_pos : 0 < youngRow lam (i : Nat) := by
      have hmid_eq :
          youngRow (twoStepFirstChild lam p) p.second.1 =
            youngRow lam p.second.1 := by
        rw [twoStepFirstChild, youngRow_deleteRemovableRowDiagram]
        simp [hrows.symm]
      rw [hi_second]
      rwa [hmid_eq] at hmid_pos
    simp [hi_second, hrows.symm]
    omega
  · by_cases hi_first : (i : Nat) = p.first.1
    · have hlam_pos : 0 < youngRow lam (i : Nat) := by
        rw [hi_first]
        exact removableRow_pos p.first.2
      simp [hi_first, hrows]
      omega
    · simp [hi_second, hi_first]

theorem deleteTwoRemovableRows_horizontal_of_same_row {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (p : TwoStepRemovableRows lam)
    (hrows : p.first.1 = p.second.1) :
    IsHorizontalTwoStripChild lam (deleteTwoRemovableRowsDiagram lam p) := by
  refine ⟨by omega, deleteTwoRemovableRows_isYoungSubdiagram lam p, ?_⟩
  intro i
  rw [youngRow_deleteTwoRemovableRowsDiagram_eq_parent]
  by_cases hi : (i : Nat) = p.first.1
  · have hmid_succ :
        youngRow (deleteRemovableRowDiagram lam p.first.1 p.first.2)
          (p.first.1 + 1) =
          youngRow lam (p.first.1 + 1) := by
      rw [youngRow_deleteRemovableRowDiagram]
      simp
    have hmid_self :
        youngRow (deleteRemovableRowDiagram lam p.first.1 p.first.2)
          p.first.1 =
          youngRow lam p.first.1 - 1 := by
      rw [youngRow_deleteRemovableRowDiagram]
      simp
    have hrem := p.second.2
    unfold IsRemovableRow at hrem
    rw [← hrows, hmid_succ, hmid_self] at hrem
    rw [hi]
    rw [← hrows]
    simp
    omega
  · have hi_second : (i : Nat) ≠ p.second.1 := by
      intro h
      exact hi (h.trans hrows.symm)
    have hmono := youngRow_succ_le lam (i : Nat)
    simp [hi, hi_second]
    exact hmono

theorem deleteTwoRemovableRows_horizontal_or_vertical {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (p : TwoStepRemovableRows lam) :
    IsHorizontalTwoStripChild lam (deleteTwoRemovableRowsDiagram lam p) ∨
      IsVerticalTwoStripChild lam (deleteTwoRemovableRowsDiagram lam p) := by
  by_cases hrows : p.first.1 = p.second.1
  · exact Or.inl (deleteTwoRemovableRows_horizontal_of_same_row lam p hrows)
  · exact Or.inr (deleteTwoRemovableRows_vertical_of_distinct_rows lam p hrows)

theorem deleteTwoRemovableRows_mem_horizontal_or_vertical_sized {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (p : TwoStepRemovableRows lam) :
    deleteTwoRemovableRowsDiagram lam p ∈ horizontalTwoStripChildrenSized lam ∨
      deleteTwoRemovableRowsDiagram lam p ∈ verticalTwoStripChildrenSized lam := by
  classical
  rcases deleteTwoRemovableRows_horizontal_or_vertical lam p with h | h
  · left
    simp [horizontalTwoStripChildrenSized, h]
  · right
    simp [verticalTwoStripChildrenSized, h]

theorem deleteTwoRemovableRows_horizontal_of_first_lt_second {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (p : TwoStepRemovableRows lam)
    (hlt : p.first.1 < p.second.1) :
    IsHorizontalTwoStripChild lam (deleteTwoRemovableRowsDiagram lam p) := by
  refine ⟨by omega, deleteTwoRemovableRows_isYoungSubdiagram lam p, ?_⟩
  intro i
  rw [youngRow_deleteTwoRemovableRowsDiagram_eq_parent]
  by_cases hi_first : (i : Nat) = p.first.1
  · have hrem := p.first.2
    unfold IsRemovableRow at hrem
    have hi_second : (i : Nat) ≠ p.second.1 := by omega
    have hne_fs : p.first.1 ≠ p.second.1 := by omega
    rw [hi_first]
    simp [hne_fs]
    omega
  · by_cases hi_second : (i : Nat) = p.second.1
    · have hmid_succ :
          youngRow (deleteRemovableRowDiagram lam p.first.1 p.first.2)
            (p.second.1 + 1) =
            youngRow lam (p.second.1 + 1) := by
        rw [youngRow_deleteRemovableRowDiagram]
        have hne : p.second.1 + 1 ≠ p.first.1 := by omega
        simp [hne]
      have hmid_self :
          youngRow (deleteRemovableRowDiagram lam p.first.1 p.first.2)
            p.second.1 =
            youngRow lam p.second.1 := by
        rw [youngRow_deleteRemovableRowDiagram]
        have hne : p.second.1 ≠ p.first.1 := by omega
        simp [hne]
      have hrem := p.second.2
      unfold IsRemovableRow at hrem
      rw [hmid_succ, hmid_self] at hrem
      have hne_sf : p.second.1 ≠ p.first.1 := by omega
      rw [hi_second]
      simp [hne_sf]
      omega
    · have hmono := youngRow_succ_le lam (i : Nat)
      simp [hi_first, hi_second]
      exact hmono

theorem deleteTwoRemovableRows_horizontal_of_first_le_second {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (p : TwoStepRemovableRows lam)
    (hle : p.first.1 <= p.second.1) :
    IsHorizontalTwoStripChild lam (deleteTwoRemovableRowsDiagram lam p) := by
  by_cases hrows : p.first.1 = p.second.1
  · exact deleteTwoRemovableRows_horizontal_of_same_row lam p hrows
  · have hlt : p.first.1 < p.second.1 := by omega
    exact deleteTwoRemovableRows_horizontal_of_first_lt_second lam p hlt

theorem deleteTwoRemovableRows_vertical_of_second_lt_first {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (p : TwoStepRemovableRows lam)
    (hlt : p.second.1 < p.first.1) :
    IsVerticalTwoStripChild lam (deleteTwoRemovableRowsDiagram lam p) := by
  exact deleteTwoRemovableRows_vertical_of_distinct_rows lam p (by omega)

noncomputable def twoStepToTaggedTwoStripChild {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) :
    TwoStepRemovableRows lam → TaggedTwoStripChildrenSized lam :=
  fun p =>
    if hle : p.first.1 <= p.second.1 then
      Sum.inl ⟨deleteTwoRemovableRowsDiagram lam p, by
        simp [horizontalTwoStripChildrenSized,
          deleteTwoRemovableRows_horizontal_of_first_le_second lam p hle]⟩
    else
      Sum.inr ⟨deleteTwoRemovableRowsDiagram lam p, by
        have hlt : p.second.1 < p.first.1 := by omega
        simp [verticalTwoStripChildrenSized,
          deleteTwoRemovableRows_vertical_of_second_lt_first lam p hlt]⟩

theorem taggedTwoStripChildDiagram_twoStepToTagged {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (p : TwoStepRemovableRows lam) :
    taggedTwoStripChildDiagram (twoStepToTaggedTwoStripChild lam p) =
      deleteTwoRemovableRowsDiagram lam p := by
  by_cases hle : p.first.1 <= p.second.1 <;>
    simp [twoStepToTaggedTwoStripChild, hle, taggedTwoStripChildDiagram]

noncomputable def horizontalTaggedChildToTwoStep {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1))
    (x : {mu : YoungDiagram n // mu ∈ horizontalTwoStripChildrenSized lam}) :
    TwoStepRemovableRows lam where
  first := firstRemovableRowOfHorizontalTaggedChild lam x
  second :=
    oneBoxChildToRemovableRowSized
      (deleteRemovableRowDiagram lam
        (firstRemovableRowOfHorizontalTaggedChild lam x).1
        (firstRemovableRowOfHorizontalTaggedChild lam x).2)
      ⟨x.1, horizontalTaggedChild_after_firstDeletion_mem_oneBoxChildrenSized lam x⟩

noncomputable def verticalTaggedChildToTwoStep {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1))
    (x : {mu : YoungDiagram n // mu ∈ verticalTwoStripChildrenSized lam}) :
    TwoStepRemovableRows lam where
  first := firstRemovableRowOfVerticalTaggedChild lam x
  second :=
    oneBoxChildToRemovableRowSized
      (deleteRemovableRowDiagram lam
        (firstRemovableRowOfVerticalTaggedChild lam x).1
        (firstRemovableRowOfVerticalTaggedChild lam x).2)
      ⟨x.1, verticalTaggedChild_after_firstDeletion_mem_oneBoxChildrenSized lam x⟩

theorem deleteTwoRemovableRowsDiagram_horizontalTaggedChildToTwoStep
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (x : {mu : YoungDiagram n // mu ∈ horizontalTwoStripChildrenSized lam}) :
    deleteTwoRemovableRowsDiagram lam
      (horizontalTaggedChildToTwoStep lam x) = x.1 := by
  unfold horizontalTaggedChildToTwoStep deleteTwoRemovableRowsDiagram
  exact removableRowToOneBoxChild_oneBoxChildToRemovableRowSized
    (deleteRemovableRowDiagram lam
      (firstRemovableRowOfHorizontalTaggedChild lam x).1
      (firstRemovableRowOfHorizontalTaggedChild lam x).2)
    ⟨x.1, horizontalTaggedChild_after_firstDeletion_mem_oneBoxChildrenSized lam x⟩

theorem deleteTwoRemovableRowsDiagram_verticalTaggedChildToTwoStep
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (x : {mu : YoungDiagram n // mu ∈ verticalTwoStripChildrenSized lam}) :
    deleteTwoRemovableRowsDiagram lam
      (verticalTaggedChildToTwoStep lam x) = x.1 := by
  unfold verticalTaggedChildToTwoStep deleteTwoRemovableRowsDiagram
  exact removableRowToOneBoxChild_oneBoxChildToRemovableRowSized
    (deleteRemovableRowDiagram lam
      (firstRemovableRowOfVerticalTaggedChild lam x).1
      (firstRemovableRowOfVerticalTaggedChild lam x).2)
    ⟨x.1, verticalTaggedChild_after_firstDeletion_mem_oneBoxChildrenSized lam x⟩

noncomputable def taggedTwoStripChildToTwoStep {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) :
    TaggedTwoStripChildrenSized lam → TwoStepRemovableRows lam
  | Sum.inl x => horizontalTaggedChildToTwoStep lam x
  | Sum.inr x => verticalTaggedChildToTwoStep lam x

theorem deleteTwoRemovableRowsDiagram_taggedTwoStripChildToTwoStep
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (x : TaggedTwoStripChildrenSized lam) :
    deleteTwoRemovableRowsDiagram lam
      (taggedTwoStripChildToTwoStep lam x) =
      taggedTwoStripChildDiagram x := by
  cases x with
  | inl x =>
      exact deleteTwoRemovableRowsDiagram_horizontalTaggedChildToTwoStep lam x
  | inr x =>
      exact deleteTwoRemovableRowsDiagram_verticalTaggedChildToTwoStep lam x

noncomputable def twoStepFirstDeletionEquiv {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (p : TwoStepRemovableRows lam) :
    {T : StandardYoungTableau lam //
      TableauMaxAt T (firstDeletedCornerOfTwoStep lam p)} ≃
      StandardYoungTableau (twoStepFirstChild lam p) :=
  oneBoxDeletionTableauxEquivChildTableauxOfOneBoxChildRow
    (twoStepFirstChild_isOneBoxChild lam p)
    (twoStepFirstChild_row_form lam p)

noncomputable def twoStepSecondDeletionEquiv {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (p : TwoStepRemovableRows lam) :
    {T : StandardYoungTableau (twoStepFirstChild lam p) //
      TableauMaxAt T (secondDeletedCornerOfTwoStepInChild lam p)} ≃
      StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p) :=
  oneBoxDeletionTableauxEquivChildTableauxOfOneBoxChildRow
    (twoStepSecondChild_isOneBoxChild lam p)
    (twoStepSecondChild_row_form lam p)

/-- Parent tableaux whose largest entry follows the first deletion of `p` and
whose next largest entry follows the second deletion of `p`. -/
abbrev TwoStepDeletionTableaux {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (p : TwoStepRemovableRows lam) :=
  {T : {T : StandardYoungTableau lam //
      TableauMaxAt T (firstDeletedCornerOfTwoStep lam p)} //
    TableauMaxAt (twoStepFirstDeletionEquiv lam p T)
      (secondDeletedCornerOfTwoStepInChild lam p)}

noncomputable instance twoStepDeletionTableauxFintype {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (p : TwoStepRemovableRows lam) :
    Fintype (TwoStepDeletionTableaux lam p) := by
  classical
  infer_instance

noncomputable def twoStepDeletionTableauxEquivChildTableaux {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (p : TwoStepRemovableRows lam) :
    TwoStepDeletionTableaux lam p ≃
      StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p) :=
  ((twoStepFirstDeletionEquiv lam p).subtypeEquiv
      (fun _ => Iff.rfl)).trans
    (twoStepSecondDeletionEquiv lam p)

theorem card_twoStepDeletionTableaux_eq_child {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (p : TwoStepRemovableRows lam) :
    Fintype.card (TwoStepDeletionTableaux lam p) =
      Fintype.card
        (StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p)) := by
  classical
  exact Fintype.card_congr
    (twoStepDeletionTableauxEquivChildTableaux lam p)

theorem tableauDim_fixed_twoStepDeletion {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) (p : TwoStepRemovableRows lam) :
    ((Fintype.card (TwoStepDeletionTableaux lam p) : Nat) : ℝ) =
      tableauDim (deleteTwoRemovableRowsDiagram lam p) := by
  rw [tableauDim, tableauDimNat, card_twoStepDeletionTableaux_eq_child]

theorem tableauDim_eq_sum_twoStepRemovableRows {n : Nat}
    (lam : YoungDiagram ((n + 1) + 1)) :
    tableauDim lam =
      ∑ p : TwoStepRemovableRows lam,
        tableauDim (deleteTwoRemovableRowsDiagram lam p) := by
  classical
  calc
    tableauDim lam =
        ∑ r : RemovableRow lam,
          tableauDim (removableRowToOneBoxChild lam r) := by
      exact tableauDim_eq_sum_removableRow_children lam
    _ =
        ∑ r : RemovableRow lam,
          ∑ s : RemovableRow (removableRowToOneBoxChild lam r),
            tableauDim
              (removableRowToOneBoxChild
                (removableRowToOneBoxChild lam r) s) := by
      refine Finset.sum_congr rfl ?_
      intro r _hr
      exact tableauDim_eq_sum_removableRow_children
        (removableRowToOneBoxChild lam r)
    _ =
        ∑ x : Sigma (fun r : RemovableRow lam =>
          RemovableRow (removableRowToOneBoxChild lam r)),
            tableauDim
              (removableRowToOneBoxChild
                (removableRowToOneBoxChild lam x.1) x.2) := by
      exact (Fintype.sum_sigma
        (fun x : Sigma (fun r : RemovableRow lam =>
          RemovableRow (removableRowToOneBoxChild lam r)) =>
          tableauDim
            (removableRowToOneBoxChild
              (removableRowToOneBoxChild lam x.1) x.2))).symm
    _ =
        ∑ p : TwoStepRemovableRows lam,
          tableauDim (deleteTwoRemovableRowsDiagram lam p) := by
      exact (Fintype.sum_equiv
        (twoStepRemovableRowsEquivSigma lam)
        (fun p : TwoStepRemovableRows lam =>
          tableauDim (deleteTwoRemovableRowsDiagram lam p))
        (fun x : Sigma (fun r : RemovableRow lam =>
          RemovableRow (removableRowToOneBoxChild lam r)) =>
          tableauDim
            (removableRowToOneBoxChild
              (removableRowToOneBoxChild lam x.1) x.2))
        (fun _ => rfl)).symm

def deleteMaxAtMaxRemovableRow {n : Nat}
    {lam : YoungDiagram (n + 1)} (T : StandardYoungTableau lam) :
    StandardYoungTableau
      (removableRowToOneBoxChild lam (maxRemovableRow T)) :=
  oneBoxDeletionTableauxEquivChildTableauxOfOneBoxChildRow
    (removableRowToOneBoxChild_isOneBoxChild lam (maxRemovableRow T))
    (row_form_deleteRemovableRowDiagram lam (maxRemovableRow T).2)
    ⟨T, tableauMaxAt_deletedCorner_maxRemovableRow T⟩

def twoStepDataOfTableau {n : Nat}
    {lam : YoungDiagram ((n + 1) + 1)}
    (T : StandardYoungTableau lam) : TwoStepRemovableRows lam where
  first := maxRemovableRow T
  second := maxRemovableRow (deleteMaxAtMaxRemovableRow T)

def tableau_mem_twoStepDataOfTableau {n : Nat}
    {lam : YoungDiagram ((n + 1) + 1)}
    (T : StandardYoungTableau lam) :
    TwoStepDeletionTableaux lam (twoStepDataOfTableau T) :=
  ⟨⟨T, tableauMaxAt_deletedCorner_maxRemovableRow T⟩,
    tableauMaxAt_deletedCorner_maxRemovableRow
      (deleteMaxAtMaxRemovableRow T)⟩

@[simp] theorem twoStepDataOfTableau_first {n : Nat}
    {lam : YoungDiagram ((n + 1) + 1)}
    (T : StandardYoungTableau lam) :
    (twoStepDataOfTableau T).first = maxRemovableRow T := by
  rfl

@[simp] theorem twoStepDataOfTableau_second {n : Nat}
    {lam : YoungDiagram ((n + 1) + 1)}
    (T : StandardYoungTableau lam) :
    (twoStepDataOfTableau T).second =
      maxRemovableRow (deleteMaxAtMaxRemovableRow T) := by
  rfl

@[simp] theorem tableau_mem_twoStepDataOfTableau_parent {n : Nat}
    {lam : YoungDiagram ((n + 1) + 1)}
    (T : StandardYoungTableau lam) :
    (tableau_mem_twoStepDataOfTableau T).1.1 = T := by
  rfl

end DictatorshipTesting
