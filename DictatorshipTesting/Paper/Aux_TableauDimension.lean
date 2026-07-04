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

abbrev RemovableRow {n : Nat} (lam : YoungDiagram (n + 1)) :=
  {r : Nat // IsRemovableRow lam r}

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

end DictatorshipTesting
