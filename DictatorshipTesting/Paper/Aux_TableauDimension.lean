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

end DictatorshipTesting
