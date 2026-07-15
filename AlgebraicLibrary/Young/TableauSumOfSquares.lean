import AlgebraicLibrary.Young.TableauDimension

/-!
# Young-tableau square sums

This file develops the rank-generic Young-lattice combinatorics needed to prove
that the sum of the squared numbers of standard tableaux is a factorial.  The
first layer exposes one-box lower and upper covers and restates the existing
tableau-deletion recursion over natural numbers.
-/

noncomputable section

open scoped BigOperators

namespace AlgebraicLibrary

/-- The Young diagrams obtained by deleting one box from `lam`. -/
def youngLowerCovers {n : Nat} (lam : YoungDiagram (n + 1)) :
    Finset (YoungDiagram n) :=
  oneBoxChildrenSized lam

/-- The Young diagrams obtained by adding one box to `mu`. -/
def youngUpperCovers {n : Nat} (mu : YoungDiagram n) :
    Finset (YoungDiagram (n + 1)) := by
  classical
  exact Finset.univ.filter (fun lam : YoungDiagram (n + 1) =>
    IsOneBoxChild lam mu)

@[simp] theorem mem_youngLowerCovers_iff {n : Nat}
    {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n} :
    mu ∈ youngLowerCovers lam ↔ IsOneBoxChild lam mu := by
  simp [youngLowerCovers, mem_oneBoxChildrenSized_iff]

@[simp] theorem mem_youngUpperCovers_iff {n : Nat}
    {mu : YoungDiagram n} {lam : YoungDiagram (n + 1)} :
    lam ∈ youngUpperCovers mu ↔ IsOneBoxChild lam mu := by
  simp [youngUpperCovers]

theorem mem_youngLowerCovers_iff_mem_youngUpperCovers {n : Nat}
    {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n} :
    mu ∈ youngLowerCovers lam ↔ lam ∈ youngUpperCovers mu := by
  simp

/-- Summing over removable rows is the same as summing over lower covers. -/
theorem sum_removableRows_eq_sum_lowerCovers {n : Nat}
    (lam : YoungDiagram (n + 1)) (f : YoungDiagram n → Nat) :
    (∑ r : RemovableRow lam, f (removableRowToOneBoxChild lam r)) =
      (youngLowerCovers lam).sum f := by
  classical
  have hsumSubtype :
      (∑ mu : {mu : YoungDiagram n // mu ∈ youngLowerCovers lam}, f mu.1) =
        (youngLowerCovers lam).sum f := by
    rw [Finset.univ_eq_attach]
    exact Finset.sum_attach (youngLowerCovers lam) f
  exact (Fintype.sum_equiv
    (removableRowsEquivOneBoxChildren lam)
    (fun r : RemovableRow lam => f (removableRowToOneBoxChild lam r))
    (fun mu : {mu : YoungDiagram n // mu ∈ youngLowerCovers lam} => f mu.1)
    (fun _ => rfl)).trans hsumSubtype

/-- Natural-number form of the generic one-box tableau-deletion recursion. -/
theorem tableauDimNat_eq_sum_lowerCovers {n : Nat}
    (lam : YoungDiagram (n + 1)) :
    tableauDimNat lam =
      (youngLowerCovers lam).sum (fun mu => tableauDimNat mu) := by
  classical
  rw [tableauDimNat_eq_card]
  rw [card_standardYoungTableau_eq_sum_removableRow_children lam]
  change
    (∑ r : RemovableRow lam,
      tableauDimNat (removableRowToOneBoxChild lam r)) =
      (youngLowerCovers lam).sum (fun mu => tableauDimNat mu)
  exact sum_removableRows_eq_sum_lowerCovers lam tableauDimNat

/-- Row `r` is addable when increasing it by one preserves weak decrease.
The bound on `r` is carried separately by `AddableRow`. -/
def IsAddableRow {n : Nat} (mu : YoungDiagram n) (r : Nat) : Prop :=
  r = 0 ∨ youngRow mu r < youngRow mu (r - 1)

/-- Addable rows of a diagram of size `n`.  Row `n` is included so that a new
last row may be added to the one-column diagram. -/
abbrev AddableRow {n : Nat} (mu : YoungDiagram n) :=
  {r : Fin (n + 1) // IsAddableRow mu r}

noncomputable instance addableRowFintype {n : Nat}
    (mu : YoungDiagram n) : Fintype (AddableRow mu) := by
  classical
  exact Fintype.ofFinite _

/-- Row lengths after adding one box in row `r`. -/
def addAddableRowLength {n : Nat} (mu : YoungDiagram n)
    (r i : Nat) : Nat :=
  if i = r then youngRow mu r + 1 else youngRow mu i

theorem addAddableRowLength_lt {n : Nat} (mu : YoungDiagram n)
    (r : Fin (n + 1)) (i : Nat) :
    addAddableRowLength mu r i < n + 2 := by
  unfold addAddableRowLength
  split
  · have hle := youngRow_le_size_aux mu (r : Nat)
    omega
  · have hle := youngRow_le_size_aux mu i
    omega

theorem addAddableRowLength_monotone {n : Nat} (mu : YoungDiagram n)
    (r : Fin (n + 1)) (hr : IsAddableRow mu r)
    {i j : Nat} (hij : i ≤ j) :
    addAddableRowLength mu r j ≤ addAddableRowLength mu r i := by
  unfold addAddableRowLength
  by_cases hir : i = (r : Nat)
  · subst i
    by_cases hjr : j = (r : Nat)
    · subst j
      simp
    · have hrow : youngRow mu j ≤ youngRow mu (r : Nat) :=
        youngRow_le_of_le mu hij
      simp [hjr]
      omega
  · by_cases hjr : j = (r : Nat)
    · subst j
      have hirlt : i < (r : Nat) := by omega
      rcases hr with hr0 | hrstep
      · omega
      · have hle : (r : Nat) - 1 ≥ i := by omega
        have hrow : youngRow mu ((r : Nat) - 1) ≤ youngRow mu i :=
          youngRow_le_of_le mu hle
        simp [hir]
        omega
    · have hrow : youngRow mu j ≤ youngRow mu i :=
        youngRow_le_of_le mu hij
      simp [hir, hjr]
      exact hrow

theorem sum_addAddableRowLength {n : Nat} (mu : YoungDiagram n)
    (r : Fin (n + 1)) :
    (Finset.range (n + 1)).sum (fun i => addAddableRowLength mu r i) =
      n + 1 := by
  let s := Finset.range (n + 1)
  have hrmem : (r : Nat) ∈ s := Finset.mem_range.mpr r.isLt
  have hsplit_add :=
    Finset.sum_erase_add s (fun i => addAddableRowLength mu r i) hrmem
  have hsplit_old :=
    Finset.sum_erase_add s (fun i => youngRow mu i) hrmem
  have herase :
      (s.erase (r : Nat)).sum (fun i => addAddableRowLength mu r i) =
        (s.erase (r : Nat)).sum (fun i => youngRow mu i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hir : i ≠ (r : Nat) := (Finset.mem_erase.mp hi).1
    simp [addAddableRowLength, hir]
  have hold : s.sum (fun i => youngRow mu i) = n := by
    simpa [s] using youngRow_sum_range_succ mu
  have hadd : addAddableRowLength mu r r = youngRow mu r + 1 := by
    simp [addAddableRowLength]
  change s.sum (fun i => addAddableRowLength mu r i) = n + 1
  rw [← hsplit_add, herase, hadd]
  rw [← hsplit_old] at hold
  omega

/-- Add one box in an addable row. -/
def addAddableRowDiagram {n : Nat} (mu : YoungDiagram n)
    (r : AddableRow mu) : YoungDiagram (n + 1) where
  row := fun i =>
    ⟨addAddableRowLength mu r.1 i,
      addAddableRowLength_lt mu r.1 i⟩
  nonincreasing := by
    intro i j hij
    change addAddableRowLength mu r.1 j ≤ addAddableRowLength mu r.1 i
    exact addAddableRowLength_monotone mu r.1 r.2 hij
  sum_rows := by
    have hfin :
        (Finset.univ.sum
            (fun i : Fin (n + 1) => addAddableRowLength mu r.1 i)) =
          (Finset.range (n + 1)).sum
            (fun i => addAddableRowLength mu r.1 i) := by
      exact Fin.sum_univ_eq_sum_range
        (fun i => addAddableRowLength mu r.1 i) (n + 1)
    rw [hfin]
    exact sum_addAddableRowLength mu r.1

theorem youngRow_addAddableRowDiagram {n : Nat} (mu : YoungDiagram n)
    (r : AddableRow mu) (i : Nat) :
    youngRow (addAddableRowDiagram mu r) i =
      if i = (r : Nat) then youngRow mu r + 1 else youngRow mu i := by
  by_cases hi : i < n + 1
  · simp [youngRow, addAddableRowDiagram, addAddableRowLength, hi]
  · have hir : i ≠ (r : Nat) := by omega
    have hi_mu : ¬i < n := by omega
    simp [youngRow, hi, hi_mu, hir]

theorem addAddableRowDiagram_isOneBoxChild {n : Nat}
    (mu : YoungDiagram n) (r : AddableRow mu) :
    IsOneBoxChild (addAddableRowDiagram mu r) mu := by
  refine ⟨rfl, ?_⟩
  intro i
  rw [youngRow_addAddableRowDiagram mu r i]
  by_cases hir : (i : Nat) = (r : Nat)
  · rw [if_pos hir]
    have hroweq : youngRow mu (i : Nat) = youngRow mu (r : Nat) :=
      congrArg (youngRow mu) hir
    omega
  · rw [if_neg hir]

theorem row_form_addAddableRowDiagram {n : Nat}
    (mu : YoungDiagram n) (r : AddableRow mu) :
    youngRow (addAddableRowDiagram mu r) r = youngRow mu r + 1 ∧
      ∀ i : Nat, i ≠ (r : Nat) →
        youngRow (addAddableRowDiagram mu r) i = youngRow mu i := by
  constructor
  · simp [youngRow_addAddableRowDiagram]
  · intro i hi
    simp [youngRow_addAddableRowDiagram, hi]

theorem addableRow_isRemovable_after_add {n : Nat}
    (mu : YoungDiagram n) (r : AddableRow mu) :
    IsRemovableRow (addAddableRowDiagram mu r) r := by
  exact isRemovableRow_of_oneBoxChild_row
    (addAddableRowDiagram_isOneBoxChild mu r)
    (row_form_addAddableRowDiagram mu r)

/-- Recover the changed row from an upper cover. -/
noncomputable def upperCoverToAddableRow {n : Nat}
    (mu : YoungDiagram n)
    (lam : {lam : YoungDiagram (n + 1) // lam ∈ youngUpperCovers mu}) :
    AddableRow mu := by
  have hchild : IsOneBoxChild lam.1 mu :=
    mem_youngUpperCovers_iff.mp lam.2
  let hrow := exists_removableRow_of_oneBoxChild hchild
  let r : Nat := Classical.choose hrow
  have hr := Classical.choose_spec hrow
  have hrlt : r < n + 1 := removableRow_lt_size hr.1
  refine ⟨⟨r, hrlt⟩, ?_⟩
  change r = 0 ∨ youngRow mu r < youngRow mu (r - 1)
  by_cases hr0 : r = 0
  · exact Or.inl hr0
  · right
    have hmono : youngRow lam.1 r ≤ youngRow lam.1 (r - 1) :=
      youngRow_le_of_le lam.1 (by omega)
    have hother : youngRow lam.1 (r - 1) = youngRow mu (r - 1) :=
      hr.2.2 (r - 1) (by omega)
    have hmain : youngRow lam.1 r = youngRow mu r + 1 := hr.2.1
    omega

theorem upperCoverToAddableRow_row_form {n : Nat}
    (mu : YoungDiagram n)
    (lam : {lam : YoungDiagram (n + 1) // lam ∈ youngUpperCovers mu}) :
    youngRow lam.1 (upperCoverToAddableRow mu lam) =
        youngRow mu (upperCoverToAddableRow mu lam) + 1 ∧
      ∀ i : Nat, i ≠ (upperCoverToAddableRow mu lam : Nat) →
        youngRow lam.1 i = youngRow mu i := by
  classical
  unfold upperCoverToAddableRow
  dsimp
  have hchild : IsOneBoxChild lam.1 mu :=
    mem_youngUpperCovers_iff.mp lam.2
  let hrow := exists_removableRow_of_oneBoxChild hchild
  exact (Classical.choose_spec hrow).2

theorem upperCoverToAddableRow_addAddableRowDiagram {n : Nat}
    (mu : YoungDiagram n) (r : AddableRow mu) :
    upperCoverToAddableRow mu
        ⟨addAddableRowDiagram mu r,
          mem_youngUpperCovers_iff.mpr
            (addAddableRowDiagram_isOneBoxChild mu r)⟩ = r := by
  apply Subtype.ext
  apply Fin.ext
  let lam : {lam : YoungDiagram (n + 1) // lam ∈ youngUpperCovers mu} :=
    ⟨addAddableRowDiagram mu r,
      mem_youngUpperCovers_iff.mpr
        (addAddableRowDiagram_isOneBoxChild mu r)⟩
  have hchosen := upperCoverToAddableRow_row_form mu lam
  have hgiven := row_form_addAddableRowDiagram mu r
  rcases existsUnique_row_of_oneBoxChild
      (addAddableRowDiagram_isOneBoxChild mu r) with
    ⟨u, _hu, huniq⟩
  have hchosen_eq : (upperCoverToAddableRow mu lam : Nat) = u :=
    huniq _ hchosen
  have hgiven_eq : (r : Nat) = u := huniq _ hgiven
  exact hchosen_eq.trans hgiven_eq.symm

theorem addAddableRowDiagram_upperCoverToAddableRow {n : Nat}
    (mu : YoungDiagram n)
    (lam : {lam : YoungDiagram (n + 1) // lam ∈ youngUpperCovers mu}) :
    addAddableRowDiagram mu (upperCoverToAddableRow mu lam) = lam.1 := by
  apply youngDiagram_ext_youngRow
  intro i
  have hchosen := upperCoverToAddableRow_row_form mu lam
  rw [youngRow_addAddableRowDiagram]
  by_cases hir : i = (upperCoverToAddableRow mu lam : Nat)
  · rw [if_pos hir]
    subst i
    exact hchosen.1.symm
  · rw [if_neg hir]
    exact (hchosen.2 i hir).symm

/-- Adding a box in an addable row parametrizes all one-box upper covers. -/
noncomputable def addableRowsEquivUpperCovers {n : Nat}
    (mu : YoungDiagram n) :
    AddableRow mu ≃ {lam : YoungDiagram (n + 1) // lam ∈ youngUpperCovers mu} where
  toFun r :=
    ⟨addAddableRowDiagram mu r,
      mem_youngUpperCovers_iff.mpr
        (addAddableRowDiagram_isOneBoxChild mu r)⟩
  invFun lam := upperCoverToAddableRow mu lam
  left_inv r := upperCoverToAddableRow_addAddableRowDiagram mu r
  right_inv lam := by
    apply Subtype.ext
    exact addAddableRowDiagram_upperCoverToAddableRow mu lam

/-- Summing over addable rows is the same as summing over upper covers. -/
theorem sum_addableRows_eq_sum_upperCovers {n : Nat}
    (mu : YoungDiagram n) (f : YoungDiagram (n + 1) → Nat) :
    (∑ r : AddableRow mu, f (addAddableRowDiagram mu r)) =
      (youngUpperCovers mu).sum f := by
  classical
  have hsumSubtype :
      (∑ lam : {lam : YoungDiagram (n + 1) // lam ∈ youngUpperCovers mu},
        f lam.1) = (youngUpperCovers mu).sum f := by
    rw [Finset.univ_eq_attach]
    exact Finset.sum_attach (youngUpperCovers mu) f
  exact (Fintype.sum_equiv
    (addableRowsEquivUpperCovers mu)
    (fun r : AddableRow mu => f (addAddableRowDiagram mu r))
    (fun lam : {lam : YoungDiagram (n + 1) // lam ∈ youngUpperCovers mu} =>
      f lam.1)
    (fun _ => rfl)).trans hsumSubtype

/-- Except for the new top row, addable rows are obtained by shifting a
removable row down by one. -/
noncomputable def addableRowToOptionRemovableRow {n : Nat}
    (mu : YoungDiagram (n + 1)) :
    AddableRow mu → Option (RemovableRow mu) := fun r => by
  by_cases hr0 : (r : Nat) = 0
  · exact none
  · refine some ⟨(r : Nat) - 1, ?_⟩
    have hadd : youngRow mu r < youngRow mu ((r : Nat) - 1) :=
      r.2.resolve_left hr0
    change youngRow mu ((r : Nat) - 1 + 1) <
      youngRow mu ((r : Nat) - 1)
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hr0)]
    exact hadd

/-- Shift a removable row down by one to obtain an addable row; `none`
corresponds to the always-addable top row. -/
def optionRemovableRowToAddableRow {n : Nat}
    (mu : YoungDiagram (n + 1)) :
    Option (RemovableRow mu) → AddableRow mu
  | none => ⟨⟨0, by omega⟩, Or.inl rfl⟩
  | some s => by
      have hslt : s.1 < n + 1 := removableRow_lt_size s.2
      refine ⟨⟨s.1 + 1, by omega⟩, Or.inr ?_⟩
      change youngRow mu (s.1 + 1) < youngRow mu (s.1 + 1 - 1)
      simpa [IsRemovableRow] using s.2

theorem addableRowToOptionRemovableRow_optionRemovableRowToAddableRow
    {n : Nat} (mu : YoungDiagram (n + 1))
    (s : Option (RemovableRow mu)) :
    addableRowToOptionRemovableRow mu
        (optionRemovableRowToAddableRow mu s) = s := by
  classical
  cases s with
  | none =>
      simp [addableRowToOptionRemovableRow,
        optionRemovableRowToAddableRow]
  | some s =>
      simp [addableRowToOptionRemovableRow,
        optionRemovableRowToAddableRow]

theorem optionRemovableRowToAddableRow_addableRowToOptionRemovableRow
    {n : Nat} (mu : YoungDiagram (n + 1)) (r : AddableRow mu) :
    optionRemovableRowToAddableRow mu
        (addableRowToOptionRemovableRow mu r) = r := by
  classical
  by_cases hr0 : (r : Nat) = 0
  · apply Subtype.ext
    apply Fin.ext
    simp [addableRowToOptionRemovableRow,
      optionRemovableRowToAddableRow, hr0]
  · apply Subtype.ext
    apply Fin.ext
    simp [addableRowToOptionRemovableRow,
      optionRemovableRowToAddableRow, hr0]
    omega

/-- Addable rows are the optional removable rows. -/
noncomputable def addableRowsEquivOptionRemovableRows {n : Nat}
    (mu : YoungDiagram (n + 1)) :
    AddableRow mu ≃ Option (RemovableRow mu) where
  toFun := addableRowToOptionRemovableRow mu
  invFun := optionRemovableRowToAddableRow mu
  left_inv := optionRemovableRowToAddableRow_addableRowToOptionRemovableRow mu
  right_inv := addableRowToOptionRemovableRow_optionRemovableRowToAddableRow mu

theorem card_addableRows_eq_card_removableRows_add_one {n : Nat}
    (mu : YoungDiagram (n + 1)) :
    Fintype.card (AddableRow mu) = Fintype.card (RemovableRow mu) + 1 := by
  rw [Fintype.card_congr (addableRowsEquivOptionRemovableRows mu)]
  exact Fintype.card_option

theorem card_youngUpperCovers_eq_card_addableRows {n : Nat}
    (mu : YoungDiagram n) :
    (youngUpperCovers mu).card = Fintype.card (AddableRow mu) := by
  rw [← Fintype.card_coe]
  exact (Fintype.card_congr (addableRowsEquivUpperCovers mu)).symm

theorem card_youngLowerCovers_eq_card_removableRows {n : Nat}
    (mu : YoungDiagram (n + 1)) :
    (youngLowerCovers mu).card = Fintype.card (RemovableRow mu) := by
  rw [← Fintype.card_coe]
  exact (Fintype.card_congr (removableRowsEquivOneBoxChildren mu)).symm

/-- A nonempty Young diagram has one more upper cover than lower cover. -/
theorem card_youngUpperCovers_eq_card_youngLowerCovers_add_one {n : Nat}
    (mu : YoungDiagram (n + 1)) :
    (youngUpperCovers mu).card = (youngLowerCovers mu).card + 1 := by
  rw [card_youngUpperCovers_eq_card_addableRows,
    card_addableRows_eq_card_removableRows_add_one,
    card_youngLowerCovers_eq_card_removableRows]

/-- Deleting the box just added in row `r` recovers the original diagram. -/
theorem delete_addAddableRowDiagram_same {n : Nat}
    (mu : YoungDiagram n) (r : AddableRow mu) :
    deleteRemovableRowDiagram (addAddableRowDiagram mu r) r
        (addableRow_isRemovable_after_add mu r) = mu := by
  apply youngDiagram_ext_youngRow
  intro i
  rw [youngRow_deleteRemovableRowDiagram]
  by_cases hir : i = (r : Nat)
  · rw [if_pos hir, youngRow_addAddableRowDiagram]
    simp
    subst i
    omega
  · rw [if_neg hir, youngRow_addAddableRowDiagram]
    simp [hir]

/-- The deleted row is addable in the resulting child. -/
def removedRowToAddableRow {n : Nat} (mu : YoungDiagram (n + 1))
    (s : RemovableRow mu) :
    AddableRow (removableRowToOneBoxChild mu s) := by
  have hslt : s.1 < n + 1 := removableRow_lt_size s.2
  refine ⟨⟨s.1, hslt⟩, ?_⟩
  unfold IsAddableRow
  by_cases hs0 : s.1 = 0
  · exact Or.inl hs0
  · right
    have hmono : youngRow mu s.1 ≤ youngRow mu (s.1 - 1) :=
      youngRow_le_of_le mu (by omega)
    have hpos : 0 < youngRow mu s.1 := removableRow_pos s.2
    change
      youngRow (deleteRemovableRowDiagram mu s.1 s.2) s.1 <
        youngRow (deleteRemovableRowDiagram mu s.1 s.2) (s.1 - 1)
    rw [youngRow_deleteRemovableRowDiagram,
      youngRow_deleteRemovableRowDiagram]
    have hprev : s.1 - 1 ≠ s.1 := by omega
    rw [if_pos rfl, if_neg hprev]
    omega

/-- Adding back the box deleted in row `s` recovers the original diagram. -/
theorem add_removedRowToOneBoxChild_same {n : Nat}
    (mu : YoungDiagram (n + 1)) (s : RemovableRow mu) :
    addAddableRowDiagram (removableRowToOneBoxChild mu s)
        (removedRowToAddableRow mu s) = mu := by
  apply youngDiagram_ext_youngRow
  intro i
  rw [youngRow_addAddableRowDiagram]
  change
    (if i = s.1 then
      youngRow (deleteRemovableRowDiagram mu s.1 s.2) s.1 + 1
    else youngRow (deleteRemovableRowDiagram mu s.1 s.2) i) =
      youngRow mu i
  by_cases his : i = s.1
  · rw [if_pos his, youngRow_deleteRemovableRowDiagram]
    rw [if_pos rfl]
    have hpos : 0 < youngRow mu s.1 := removableRow_pos s.2
    subst i
    omega
  · rw [if_neg his, youngRow_deleteRemovableRowDiagram]
    rw [if_neg his]

/-- A removable row distinct from the added row was already removable before
the addition. -/
theorem isRemovableRow_before_add_of_ne {n : Nat}
    (mu : YoungDiagram n) (a : AddableRow mu) {s : Nat}
    (hs : IsRemovableRow (addAddableRowDiagram mu a) s)
    (hsa : s ≠ (a : Nat)) :
    IsRemovableRow mu s := by
  unfold IsRemovableRow at hs ⊢
  rw [youngRow_addAddableRowDiagram,
    youngRow_addAddableRowDiagram] at hs
  by_cases hsucc : s + 1 = (a : Nat)
  · rw [if_pos hsucc, if_neg hsa] at hs
    have haeq : youngRow mu (a : Nat) = youngRow mu (s + 1) :=
      congrArg (youngRow mu) hsucc.symm
    omega
  · rw [if_neg hsucc, if_neg hsa] at hs
    exact hs

/-- If an added diagram has a removable row other than the added row, then the
added row was not the new out-of-range last row. -/
theorem addableRow_lt_size_of_other_removable {n : Nat}
    (mu : YoungDiagram (n + 1)) (a : AddableRow mu) {s : Nat}
    (hs : IsRemovableRow (addAddableRowDiagram mu a) s)
    (hsa : s ≠ (a : Nat)) :
    (a : Nat) < n + 1 := by
  by_contra ha
  have haeq : (a : Nat) = n + 1 := by omega
  have ha0 : (a : Nat) ≠ 0 := by omega
  have hadd : youngRow mu a < youngRow mu ((a : Nat) - 1) :=
    a.2.resolve_left ha0
  have hlast_pos : 0 < youngRow mu n := by
    have hzero : youngRow mu (n + 1) = 0 := by
      simp [youngRow]
    rw [haeq, hzero] at hadd
    have hpred : n + 1 - 1 = n := by omega
    rw [hpred] at hadd
    omega
  have hs_bound : s < n + 1 := by
    have hslt : s < n + 2 := removableRow_lt_size hs
    omega
  have hs_two : 1 < youngRow mu s := by
    have hs' := hs
    unfold IsRemovableRow at hs'
    rw [youngRow_addAddableRowDiagram,
      youngRow_addAddableRowDiagram] at hs'
    by_cases hsucc : s + 1 = (a : Nat)
    · rw [if_pos hsucc, if_neg hsa] at hs'
      have haeqrow : youngRow mu (a : Nat) = 0 := by
        rw [haeq]
        simp [youngRow]
      omega
    · rw [if_neg hsucc, if_neg hsa] at hs'
      have hs_succ_le_n : s + 1 ≤ n := by omega
      have hnext_ge_last : youngRow mu n ≤ youngRow mu (s + 1) :=
        youngRow_le_of_le mu hs_succ_le_n
      omega
  have hle :
      ∀ i ∈ Finset.range (n + 1), 1 ≤ youngRow mu i := by
    intro i hi
    have hin : i ≤ n := by
      have := Finset.mem_range.mp hi
      omega
    have hrow : youngRow mu n ≤ youngRow mu i :=
      youngRow_le_of_le mu hin
    omega
  have hex :
      ∃ i ∈ Finset.range (n + 1), 1 < youngRow mu i :=
    ⟨s, Finset.mem_range.mpr hs_bound, hs_two⟩
  have hsum_lt := Finset.sum_lt_sum hle hex
  have hsum := youngRow_sum_range mu
  simp at hsum_lt
  omega

/-- In a non-diagonal up-down path, the added row remains addable after
deleting the other removable row. -/
def addableRowAfterDeletingOther {n : Nat}
    (mu : YoungDiagram (n + 1)) (a : AddableRow mu) {s : Nat}
    (hs : IsRemovableRow (addAddableRowDiagram mu a) s)
    (hsa : s ≠ (a : Nat)) :
    AddableRow
      (deleteRemovableRowDiagram mu s
        (isRemovableRow_before_add_of_ne mu a hs hsa)) := by
  let hs_mu := isRemovableRow_before_add_of_ne mu a hs hsa
  have halt := addableRow_lt_size_of_other_removable mu a hs hsa
  refine ⟨⟨(a : Nat), halt⟩, ?_⟩
  unfold IsAddableRow
  by_cases ha0 : (a : Nat) = 0
  · exact Or.inl ha0
  · right
    have hadd : youngRow mu a < youngRow mu ((a : Nat) - 1) :=
      a.2.resolve_left ha0
    change
      youngRow (deleteRemovableRowDiagram mu s hs_mu) (a : Nat) <
        youngRow (deleteRemovableRowDiagram mu s hs_mu) ((a : Nat) - 1)
    rw [youngRow_deleteRemovableRowDiagram,
      youngRow_deleteRemovableRowDiagram]
    have has : (a : Nat) ≠ s := Ne.symm hsa
    rw [if_neg has]
    by_cases hprev : (a : Nat) - 1 = s
    · rw [if_pos hprev]
      have hs' := hs
      unfold IsRemovableRow at hs'
      rw [youngRow_addAddableRowDiagram,
        youngRow_addAddableRowDiagram] at hs'
      have hsucc : s + 1 = (a : Nat) := by omega
      rw [if_pos hsucc, if_neg hsa] at hs'
      have hpos : 0 < youngRow mu s := removableRow_pos hs_mu
      omega
    · rw [if_neg hprev]
      exact hadd

/-- Distinct one-box addition and deletion operations commute. -/
theorem delete_after_add_comm_of_ne {n : Nat}
    (mu : YoungDiagram (n + 1)) (a : AddableRow mu) {s : Nat}
    (hs : IsRemovableRow (addAddableRowDiagram mu a) s)
    (hsa : s ≠ (a : Nat)) :
    deleteRemovableRowDiagram (addAddableRowDiagram mu a) s hs =
      addAddableRowDiagram
        (deleteRemovableRowDiagram mu s
          (isRemovableRow_before_add_of_ne mu a hs hsa))
        (addableRowAfterDeletingOther mu a hs hsa) := by
  let hs_mu := isRemovableRow_before_add_of_ne mu a hs hsa
  apply youngDiagram_ext_youngRow
  intro i
  rw [youngRow_deleteRemovableRowDiagram
    (addAddableRowDiagram mu a) hs i]
  rw [youngRow_addAddableRowDiagram mu a s,
    youngRow_addAddableRowDiagram mu a i]
  rw [youngRow_addAddableRowDiagram
    (deleteRemovableRowDiagram mu s hs_mu)
    (addableRowAfterDeletingOther mu a hs hsa) i]
  have haval :
      (addableRowAfterDeletingOther mu a hs hsa : Nat) = (a : Nat) := rfl
  rw [haval]
  rw [youngRow_deleteRemovableRowDiagram mu hs_mu (a : Nat),
    youngRow_deleteRemovableRowDiagram mu hs_mu i]
  by_cases his : i = s
  · rw [if_pos his]
    have hia : i ≠ (a : Nat) := by omega
    simp [his, hsa]
  · rw [if_neg his]
    by_cases hia : i = (a : Nat)
    · simp [hia, Ne.symm hsa]
    · simp [hia, his]

/-- In a non-diagonal down-up path, an addable row of the child was already
addable before deleting the other row. -/
def addableRowBeforeDelete {n : Nat}
    (mu : YoungDiagram (n + 1)) (s : RemovableRow mu)
    (b : AddableRow (removableRowToOneBoxChild mu s))
    (hbs : (b : Nat) ≠ s.1) : AddableRow mu := by
  refine ⟨⟨(b : Nat), by omega⟩, ?_⟩
  unfold IsAddableRow
  by_cases hb0 : (b : Nat) = 0
  · exact Or.inl hb0
  · right
    have hbadd :
        youngRow (removableRowToOneBoxChild mu s) b <
          youngRow (removableRowToOneBoxChild mu s) ((b : Nat) - 1) :=
      b.2.resolve_left hb0
    change youngRow mu b < youngRow mu ((b : Nat) - 1)
    change
      youngRow (deleteRemovableRowDiagram mu s.1 s.2) b <
        youngRow (deleteRemovableRowDiagram mu s.1 s.2) ((b : Nat) - 1)
      at hbadd
    rw [youngRow_deleteRemovableRowDiagram,
      youngRow_deleteRemovableRowDiagram] at hbadd
    rw [if_neg hbs] at hbadd
    by_cases hprev : (b : Nat) - 1 = s.1
    · rw [if_pos hprev] at hbadd
      have hrowprev :
          youngRow mu ((b : Nat) - 1) = youngRow mu s.1 :=
        congrArg (youngRow mu) hprev
      omega
    · rw [if_neg hprev] at hbadd
      exact hbadd

/-- After commuting a distinct down-up path, the deleted row is removable in
the diagram obtained by adding the other row first. -/
theorem removableRowAfterAddingOther {n : Nat}
    (mu : YoungDiagram (n + 1)) (s : RemovableRow mu)
    (b : AddableRow (removableRowToOneBoxChild mu s))
    (hbs : (b : Nat) ≠ s.1) :
    IsRemovableRow (addAddableRowDiagram mu
      (addableRowBeforeDelete mu s b hbs)) s.1 := by
  let a := addableRowBeforeDelete mu s b hbs
  have haval : (a : Nat) = (b : Nat) := rfl
  unfold IsRemovableRow
  rw [youngRow_addAddableRowDiagram,
    youngRow_addAddableRowDiagram]
  have hsa : s.1 ≠ (a : Nat) := by simpa [haval] using Ne.symm hbs
  rw [if_neg hsa]
  by_cases hsucc : s.1 + 1 = (a : Nat)
  · rw [if_pos hsucc]
    have hb0 : (b : Nat) ≠ 0 := by omega
    have hbadd :
        youngRow (removableRowToOneBoxChild mu s) b <
          youngRow (removableRowToOneBoxChild mu s) ((b : Nat) - 1) :=
      b.2.resolve_left hb0
    change
      youngRow (deleteRemovableRowDiagram mu s.1 s.2) b <
        youngRow (deleteRemovableRowDiagram mu s.1 s.2) ((b : Nat) - 1)
      at hbadd
    rw [youngRow_deleteRemovableRowDiagram,
      youngRow_deleteRemovableRowDiagram] at hbadd
    have hbat : (b : Nat) ≠ s.1 := hbs
    have hprev : (b : Nat) - 1 = s.1 := by omega
    rw [if_neg hbat, if_pos hprev] at hbadd
    have hpos : 0 < youngRow mu s.1 := removableRow_pos s.2
    have hrowprev :
        youngRow mu ((b : Nat) - 1) = youngRow mu s.1 :=
      congrArg (youngRow mu) hprev
    have hrowab : youngRow mu a = youngRow mu b :=
      congrArg (youngRow mu) haval
    have hrowdirect :
        youngRow mu (addableRowBeforeDelete mu s b hbs) = youngRow mu b := rfl
    omega
  · rw [if_neg hsucc]
    exact s.2

theorem addableRowAfterDeletingOther_addableRowBeforeDelete {n : Nat}
    (mu : YoungDiagram (n + 1)) (s : RemovableRow mu)
    (b : AddableRow (removableRowToOneBoxChild mu s))
    (hbs : (b : Nat) ≠ s.1) :
    addableRowAfterDeletingOther mu
        (addableRowBeforeDelete mu s b hbs)
        (removableRowAfterAddingOther mu s b hbs)
        (by
          change s.1 ≠ (b : Nat)
          exact Ne.symm hbs) = b := by
  apply Subtype.ext
  apply Fin.ext
  rfl

theorem addableRowBeforeDelete_addableRowAfterDeletingOther {n : Nat}
    (mu : YoungDiagram (n + 1)) (a : AddableRow mu) {s : Nat}
    (hs : IsRemovableRow (addAddableRowDiagram mu a) s)
    (hsa : s ≠ (a : Nat)) :
    addableRowBeforeDelete mu
        ⟨s, isRemovableRow_before_add_of_ne mu a hs hsa⟩
        (addableRowAfterDeletingOther mu a hs hsa)
        (by
          change (a : Nat) ≠ s
          exact Ne.symm hsa) = a := by
  apply Subtype.ext
  apply Fin.ext
  rfl

/-- A path that first adds and then removes one box. -/
abbrev YoungUpDownPath {n : Nat} (mu : YoungDiagram (n + 1)) :=
  Sigma fun a : AddableRow mu => RemovableRow (addAddableRowDiagram mu a)

/-- A path that first removes and then adds one box. -/
abbrev YoungDownUpPath {n : Nat} (mu : YoungDiagram (n + 1)) :=
  Sigma fun s : RemovableRow mu =>
    AddableRow (removableRowToOneBoxChild mu s)

def youngUpDownEndpoint {n : Nat} (mu : YoungDiagram (n + 1))
    (p : YoungUpDownPath mu) : YoungDiagram (n + 1) :=
  deleteRemovableRowDiagram (addAddableRowDiagram mu p.1)
    p.2.1 p.2.2

def youngDownUpEndpoint {n : Nat} (mu : YoungDiagram (n + 1))
    (p : YoungDownUpPath mu) : YoungDiagram (n + 1) :=
  addAddableRowDiagram (removableRowToOneBoxChild mu p.1) p.2

theorem youngUpDownEndpoint_eq_self_of_same_row {n : Nat}
    (mu : YoungDiagram (n + 1)) (a : AddableRow mu)
    (s : RemovableRow (addAddableRowDiagram mu a))
    (hsa : s.1 = (a : Nat)) :
    youngUpDownEndpoint mu ⟨a, s⟩ = mu := by
  have hs : s =
      ⟨(a : Nat), addableRow_isRemovable_after_add mu a⟩ := by
    apply Subtype.ext
    exact hsa
  subst s
  exact delete_addAddableRowDiagram_same mu a

theorem youngDownUpEndpoint_eq_self_of_same_row {n : Nat}
    (mu : YoungDiagram (n + 1)) (s : RemovableRow mu)
    (b : AddableRow (removableRowToOneBoxChild mu s))
    (hbs : (b : Nat) = s.1) :
    youngDownUpEndpoint mu ⟨s, b⟩ = mu := by
  have hb : b = removedRowToAddableRow mu s := by
    apply Subtype.ext
    apply Fin.ext
    exact hbs
  subst b
  exact add_removedRowToOneBoxChild_same mu s

abbrev YoungUpDownOffDiagonalPath {n : Nat}
    (mu : YoungDiagram (n + 1)) :=
  {p : YoungUpDownPath mu // youngUpDownEndpoint mu p ≠ mu}

abbrev YoungDownUpOffDiagonalPath {n : Nat}
    (mu : YoungDiagram (n + 1)) :=
  {p : YoungDownUpPath mu // youngDownUpEndpoint mu p ≠ mu}

noncomputable def upDownOffDiagonalToDownUp {n : Nat}
    (mu : YoungDiagram (n + 1)) :
    YoungUpDownOffDiagonalPath mu → YoungDownUpOffDiagonalPath mu := fun p => by
  rcases p with ⟨⟨a, s⟩, hp⟩
  have hsa : s.1 ≠ (a : Nat) := by
    intro h
    exact hp (youngUpDownEndpoint_eq_self_of_same_row mu a s h)
  let hs_mu := isRemovableRow_before_add_of_ne mu a s.2 hsa
  let s_mu : RemovableRow mu := ⟨s.1, hs_mu⟩
  let b := addableRowAfterDeletingOther mu a s.2 hsa
  let q : YoungDownUpPath mu := ⟨s_mu, b⟩
  refine ⟨q, ?_⟩
  intro hq
  have hcomm := delete_after_add_comm_of_ne mu a s.2 hsa
  apply hp
  simpa [youngUpDownEndpoint, youngDownUpEndpoint, q, s_mu, b]
    using hcomm.trans hq

noncomputable def downUpOffDiagonalToUpDown {n : Nat}
    (mu : YoungDiagram (n + 1)) :
    YoungDownUpOffDiagonalPath mu → YoungUpDownOffDiagonalPath mu := fun q => by
  rcases q with ⟨⟨s, b⟩, hq⟩
  have hbs : (b : Nat) ≠ s.1 := by
    intro h
    exact hq (youngDownUpEndpoint_eq_self_of_same_row mu s b h)
  let a := addableRowBeforeDelete mu s b hbs
  let hs := removableRowAfterAddingOther mu s b hbs
  let p : YoungUpDownPath mu := ⟨a, ⟨s.1, hs⟩⟩
  refine ⟨p, ?_⟩
  intro hp
  have hsa : s.1 ≠ (a : Nat) := by
    change s.1 ≠ (b : Nat)
    exact Ne.symm hbs
  have hcomm := delete_after_add_comm_of_ne mu a hs hsa
  have hb :=
    addableRowAfterDeletingOther_addableRowBeforeDelete mu s b hbs
  rw [hb] at hcomm
  apply hq
  simpa [youngUpDownEndpoint, youngDownUpEndpoint, p, a, hs,
    removableRowToOneBoxChild]
    using hcomm.symm.trans hp

theorem downUpOffDiagonalToUpDown_upDownOffDiagonalToDownUp {n : Nat}
    (mu : YoungDiagram (n + 1)) (p : YoungUpDownOffDiagonalPath mu) :
    downUpOffDiagonalToUpDown mu (upDownOffDiagonalToDownUp mu p) = p := by
  rcases p with ⟨⟨a, s⟩, hp⟩
  apply Subtype.ext
  apply Sigma.ext
  · apply Subtype.ext
    apply Fin.ext
    rfl
  · apply heq_of_eq
    apply Subtype.ext
    rfl

theorem upDownOffDiagonalToDownUp_downUpOffDiagonalToUpDown {n : Nat}
    (mu : YoungDiagram (n + 1)) (p : YoungDownUpOffDiagonalPath mu) :
    upDownOffDiagonalToDownUp mu (downUpOffDiagonalToUpDown mu p) = p := by
  rcases p with ⟨⟨s, b⟩, hp⟩
  apply Subtype.ext
  apply Sigma.ext
  · apply Subtype.ext
    rfl
  · apply heq_of_eq
    apply Subtype.ext
    apply Fin.ext
    rfl

/-- Non-diagonal up-down and down-up Young-lattice paths are in bijection. -/
noncomputable def youngUpDownOffDiagonalEquivDownUp {n : Nat}
    (mu : YoungDiagram (n + 1)) :
    YoungUpDownOffDiagonalPath mu ≃ YoungDownUpOffDiagonalPath mu where
  toFun := upDownOffDiagonalToDownUp mu
  invFun := downUpOffDiagonalToUpDown mu
  left_inv := downUpOffDiagonalToUpDown_upDownOffDiagonalToDownUp mu
  right_inv := upDownOffDiagonalToDownUp_downUpOffDiagonalToUpDown mu

/-- The off-diagonal path equivalence preserves the terminal diagram. -/
theorem youngUpDownOffDiagonalEquivDownUp_endpoint {n : Nat}
    (mu : YoungDiagram (n + 1)) (p : YoungUpDownOffDiagonalPath mu) :
    youngDownUpEndpoint mu
        ((youngUpDownOffDiagonalEquivDownUp mu p).1) =
      youngUpDownEndpoint mu p.1 := by
  rcases p with ⟨⟨a, s⟩, hp⟩
  have hsa : s.1 ≠ (a : Nat) := by
    intro h
    exact hp (youngUpDownEndpoint_eq_self_of_same_row mu a s h)
  exact (delete_after_add_comm_of_ne mu a s.2 hsa).symm

theorem upDown_same_row_of_endpoint_eq_self {n : Nat}
    (mu : YoungDiagram (n + 1)) (a : AddableRow mu)
    (s : RemovableRow (addAddableRowDiagram mu a))
    (hendpoint : youngUpDownEndpoint mu ⟨a, s⟩ = mu) :
    s.1 = (a : Nat) := by
  have hsform := row_form_deleteRemovableRowDiagram
    (addAddableRowDiagram mu a) s.2
  change
    youngRow (addAddableRowDiagram mu a) s.1 =
        youngRow (youngUpDownEndpoint mu ⟨a, s⟩) s.1 + 1 ∧
      ∀ t : Nat, t ≠ s.1 →
        youngRow (addAddableRowDiagram mu a) t =
          youngRow (youngUpDownEndpoint mu ⟨a, s⟩) t at hsform
  rw [hendpoint] at hsform
  have haform := row_form_addAddableRowDiagram mu a
  rcases existsUnique_row_of_oneBoxChild
      (addAddableRowDiagram_isOneBoxChild mu a) with
    ⟨r, _hr, huniq⟩
  exact (huniq s.1 hsform).trans (huniq (a : Nat) haform).symm

theorem downUp_same_row_of_endpoint_eq_self {n : Nat}
    (mu : YoungDiagram (n + 1)) (s : RemovableRow mu)
    (b : AddableRow (removableRowToOneBoxChild mu s))
    (hendpoint : youngDownUpEndpoint mu ⟨s, b⟩ = mu) :
    (b : Nat) = s.1 := by
  have hbform := row_form_addAddableRowDiagram
    (removableRowToOneBoxChild mu s) b
  change
    youngRow (youngDownUpEndpoint mu ⟨s, b⟩) b =
        youngRow (removableRowToOneBoxChild mu s) b + 1 ∧
      ∀ t : Nat, t ≠ (b : Nat) →
        youngRow (youngDownUpEndpoint mu ⟨s, b⟩) t =
          youngRow (removableRowToOneBoxChild mu s) t at hbform
  rw [hendpoint] at hbform
  have hsform := row_form_deleteRemovableRowDiagram mu s.2
  rcases existsUnique_row_of_oneBoxChild
      (removableRowToOneBoxChild_isOneBoxChild mu s) with
    ⟨r, _hr, huniq⟩
  exact (huniq (b : Nat) hbform).trans (huniq s.1 hsform).symm

abbrev YoungUpDownDiagonalPath {n : Nat}
    (mu : YoungDiagram (n + 1)) :=
  {p : YoungUpDownPath mu // youngUpDownEndpoint mu p = mu}

abbrev YoungDownUpDiagonalPath {n : Nat}
    (mu : YoungDiagram (n + 1)) :=
  {p : YoungDownUpPath mu // youngDownUpEndpoint mu p = mu}

noncomputable def addableRowsEquivUpDownDiagonalPaths {n : Nat}
    (mu : YoungDiagram (n + 1)) :
    AddableRow mu ≃ YoungUpDownDiagonalPath mu where
  toFun a :=
    ⟨⟨a, ⟨(a : Nat), addableRow_isRemovable_after_add mu a⟩⟩,
      delete_addAddableRowDiagram_same mu a⟩
  invFun p := p.1.1
  left_inv a := rfl
  right_inv p := by
    rcases p with ⟨⟨a, s⟩, hp⟩
    apply Subtype.ext
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      exact (upDown_same_row_of_endpoint_eq_self mu a s hp).symm

noncomputable def removableRowsEquivDownUpDiagonalPaths {n : Nat}
    (mu : YoungDiagram (n + 1)) :
    RemovableRow mu ≃ YoungDownUpDiagonalPath mu where
  toFun s :=
    ⟨⟨s, removedRowToAddableRow mu s⟩,
      add_removedRowToOneBoxChild_same mu s⟩
  invFun p := p.1.1
  left_inv s := rfl
  right_inv p := by
    rcases p with ⟨⟨s, b⟩, hp⟩
    apply Subtype.ext
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      apply Fin.ext
      exact (downUp_same_row_of_endpoint_eq_self mu s b hp).symm

/-- Weighted differential relation for one-box paths in the Young lattice. -/
theorem youngLattice_upDown_path_sum {n : Nat}
    (mu : YoungDiagram (n + 1)) (f : YoungDiagram (n + 1) → Nat) :
    (∑ p : YoungUpDownPath mu, f (youngUpDownEndpoint mu p)) =
      f mu + ∑ p : YoungDownUpPath mu, f (youngDownUpEndpoint mu p) := by
  classical
  have hupDiagonal :
      (∑ p : YoungUpDownDiagonalPath mu,
          f (youngUpDownEndpoint mu p.1)) =
        Fintype.card (AddableRow mu) * f mu := by
    have hreindex := Fintype.sum_equiv
      (addableRowsEquivUpDownDiagonalPaths mu)
      (fun _a : AddableRow mu => f mu)
      (fun p : YoungUpDownDiagonalPath mu =>
        f (youngUpDownEndpoint mu p.1))
      (fun a => by rw [(addableRowsEquivUpDownDiagonalPaths mu a).2])
    calc
      (∑ p : YoungUpDownDiagonalPath mu,
          f (youngUpDownEndpoint mu p.1)) =
          ∑ _a : AddableRow mu, f mu := hreindex.symm
      _ = Fintype.card (AddableRow mu) * f mu := by simp
  have hdownDiagonal :
      (∑ p : YoungDownUpDiagonalPath mu,
          f (youngDownUpEndpoint mu p.1)) =
        Fintype.card (RemovableRow mu) * f mu := by
    have hreindex := Fintype.sum_equiv
      (removableRowsEquivDownUpDiagonalPaths mu)
      (fun _s : RemovableRow mu => f mu)
      (fun p : YoungDownUpDiagonalPath mu =>
        f (youngDownUpEndpoint mu p.1))
      (fun s => by rw [(removableRowsEquivDownUpDiagonalPaths mu s).2])
    calc
      (∑ p : YoungDownUpDiagonalPath mu,
          f (youngDownUpEndpoint mu p.1)) =
          ∑ _s : RemovableRow mu, f mu := hreindex.symm
      _ = Fintype.card (RemovableRow mu) * f mu := by simp
  have hdiagonal :
      (∑ p : YoungUpDownDiagonalPath mu,
          f (youngUpDownEndpoint mu p.1)) =
        f mu + ∑ p : YoungDownUpDiagonalPath mu,
          f (youngDownUpEndpoint mu p.1) := by
    rw [hupDiagonal, hdownDiagonal,
      card_addableRows_eq_card_removableRows_add_one]
    simp [add_mul, add_comm]
  have hoffDiagonal :
      (∑ p : YoungUpDownOffDiagonalPath mu,
          f (youngUpDownEndpoint mu p.1)) =
        ∑ p : YoungDownUpOffDiagonalPath mu,
          f (youngDownUpEndpoint mu p.1) := by
    exact Fintype.sum_equiv
      (youngUpDownOffDiagonalEquivDownUp mu)
      (fun p : YoungUpDownOffDiagonalPath mu =>
        f (youngUpDownEndpoint mu p.1))
      (fun p : YoungDownUpOffDiagonalPath mu =>
        f (youngDownUpEndpoint mu p.1))
      (fun p => congrArg f
        (youngUpDownOffDiagonalEquivDownUp_endpoint mu p).symm)
  have hupSplit := Fintype.sum_subtype_add_sum_subtype
    (fun p : YoungUpDownPath mu => youngUpDownEndpoint mu p = mu)
    (fun p : YoungUpDownPath mu => f (youngUpDownEndpoint mu p))
  have hdownSplit := Fintype.sum_subtype_add_sum_subtype
    (fun p : YoungDownUpPath mu => youngDownUpEndpoint mu p = mu)
    (fun p : YoungDownUpPath mu => f (youngDownUpEndpoint mu p))
  calc
    (∑ p : YoungUpDownPath mu, f (youngUpDownEndpoint mu p)) =
        (∑ p : YoungUpDownDiagonalPath mu,
          f (youngUpDownEndpoint mu p.1)) +
        ∑ p : YoungUpDownOffDiagonalPath mu,
          f (youngUpDownEndpoint mu p.1) := hupSplit.symm
    _ = (f mu + ∑ p : YoungDownUpDiagonalPath mu,
          f (youngDownUpEndpoint mu p.1)) +
        ∑ p : YoungDownUpOffDiagonalPath mu,
          f (youngDownUpEndpoint mu p.1) := by
      rw [hdiagonal, hoffDiagonal]
    _ = f mu +
        ((∑ p : YoungDownUpDiagonalPath mu,
            f (youngDownUpEndpoint mu p.1)) +
          ∑ p : YoungDownUpOffDiagonalPath mu,
            f (youngDownUpEndpoint mu p.1)) := by
      rw [add_assoc]
    _ = f mu + ∑ p : YoungDownUpPath mu,
          f (youngDownUpEndpoint mu p) := by
      rw [hdownSplit]

theorem sum_youngUpDownPath_eq_coverSums {n : Nat}
    (mu : YoungDiagram (n + 1)) (f : YoungDiagram (n + 1) → Nat) :
    (∑ p : YoungUpDownPath mu, f (youngUpDownEndpoint mu p)) =
      (youngUpperCovers mu).sum (fun lam =>
        (youngLowerCovers lam).sum f) := by
  classical
  rw [Fintype.sum_sigma]
  calc
    (∑ a : AddableRow mu,
        ∑ s : RemovableRow (addAddableRowDiagram mu a),
          f (youngUpDownEndpoint mu ⟨a, s⟩)) =
        ∑ a : AddableRow mu,
          (youngLowerCovers (addAddableRowDiagram mu a)).sum f := by
      apply Fintype.sum_congr
      intro a
      simpa [youngUpDownEndpoint, removableRowToOneBoxChild] using
        sum_removableRows_eq_sum_lowerCovers
          (addAddableRowDiagram mu a) f
    _ = (youngUpperCovers mu).sum (fun lam =>
          (youngLowerCovers lam).sum f) := by
      exact sum_addableRows_eq_sum_upperCovers mu
        (fun lam => (youngLowerCovers lam).sum f)

theorem sum_youngDownUpPath_eq_coverSums {n : Nat}
    (mu : YoungDiagram (n + 1)) (f : YoungDiagram (n + 1) → Nat) :
    (∑ p : YoungDownUpPath mu, f (youngDownUpEndpoint mu p)) =
      (youngLowerCovers mu).sum (fun kap =>
        (youngUpperCovers kap).sum f) := by
  classical
  rw [Fintype.sum_sigma]
  calc
    (∑ s : RemovableRow mu,
        ∑ a : AddableRow (removableRowToOneBoxChild mu s),
          f (youngDownUpEndpoint mu ⟨s, a⟩)) =
        ∑ s : RemovableRow mu,
          (youngUpperCovers (removableRowToOneBoxChild mu s)).sum f := by
      apply Fintype.sum_congr
      intro s
      simpa [youngDownUpEndpoint] using
        sum_addableRows_eq_sum_upperCovers
          (removableRowToOneBoxChild mu s) f
    _ = (youngLowerCovers mu).sum (fun kap =>
          (youngUpperCovers kap).sum f) := by
      exact sum_removableRows_eq_sum_lowerCovers mu
        (fun kap => (youngUpperCovers kap).sum f)

/-- The weighted local differential relation for the Young lattice. -/
theorem youngLattice_up_down_sum {n : Nat}
    (mu : YoungDiagram (n + 1)) (f : YoungDiagram (n + 1) → Nat) :
    (youngUpperCovers mu).sum (fun lam =>
        (youngLowerCovers lam).sum f) =
      f mu + (youngLowerCovers mu).sum (fun kap =>
        (youngUpperCovers kap).sum f) := by
  rw [← sum_youngUpDownPath_eq_coverSums mu f,
    ← sum_youngDownUpPath_eq_coverSums mu f]
  exact youngLattice_upDown_path_sum mu f

private def emptyYoungDiagramForSquareSum : YoungDiagram 0 where
  row := Fin.elim0
  nonincreasing := by intro i; exact Fin.elim0 i
  sum_rows := by simp

private theorem card_youngDiagram_rank_zero :
    Fintype.card (YoungDiagram 0) = 1 := by
  have hsub : Subsingleton (YoungDiagram 0) := by
    constructor
    intro mu nu
    cases mu
    cases nu
    congr
    funext i
    exact Fin.elim0 i
  rw [Fintype.card_eq_one_iff]
  refine ⟨emptyYoungDiagramForSquareSum, ?_⟩
  intro lam
  exact @Subsingleton.elim _ hsub lam emptyYoungDiagramForSquareSum

private noncomputable def emptyStandardYoungTableauForSquareSum
    (lam : YoungDiagram 0) : StandardYoungTableau lam where
  entry := fun u => Fin.elim0 u.1.1
  bijective := by
    constructor
    · intro u
      exact Fin.elim0 u.1.1
    · intro a
      exact Fin.elim0 a
  row_strict := by
    intro u
    exact Fin.elim0 u.1.1
  col_strict := by
    intro u
    exact Fin.elim0 u.1.1

@[simp] theorem tableauDimNat_rank_zero (lam : YoungDiagram 0) :
    tableauDimNat lam = 1 := by
  rw [tableauDimNat, Fintype.card_eq_one_iff]
  refine ⟨emptyStandardYoungTableauForSquareSum lam, ?_⟩
  intro T
  apply standardYoungTableau_ext_entry
  intro u
  exact Fin.elim0 u.1.1

@[simp] theorem tableauDimNat_rank_one (lam : YoungDiagram 1) :
    tableauDimNat lam = 1 := by
  have hrow : youngRow lam 0 = 1 := by
    have h := lam.sum_rows
    rw [Fin.sum_univ_one] at h
    unfold youngRow
    norm_num
    simpa using h
  let r0 : RemovableRow lam := ⟨0, by
    change youngRow lam 1 < youngRow lam 0
    rw [hrow]
    simp [youngRow]⟩
  have hcard : Fintype.card (RemovableRow lam) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨r0, ?_⟩
    intro r
    apply Subtype.ext
    have hr := removableRow_lt_size r.2
    change r.1 = (r0 : Nat)
    simp only [r0]
    omega
  rw [tableauDimNat_eq_sum_lowerCovers]
  rw [← sum_removableRows_eq_sum_lowerCovers]
  calc
    (∑ r : RemovableRow lam,
        tableauDimNat (removableRowToOneBoxChild lam r)) =
        ∑ _r : RemovableRow lam, 1 := by
      apply Fintype.sum_congr
      intro r
      exact tableauDimNat_rank_zero _
    _ = 1 := by simp [hcard]

private theorem card_addableRows_rank_zero (mu : YoungDiagram 0) :
    Fintype.card (AddableRow mu) = 1 := by
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨0, Or.inl rfl⟩, ?_⟩
  intro r
  apply Subtype.ext
  exact Fin.eq_zero r.1

/-- Upward branching for tableau counts, derived from the Young-lattice
differential relation and downward tableau deletion. -/
theorem sum_tableauDimNat_upperCovers (n : Nat) (mu : YoungDiagram n) :
    (youngUpperCovers mu).sum tableauDimNat =
      (n + 1) * tableauDimNat mu := by
  induction n with
  | zero =>
      calc
        (youngUpperCovers mu).sum tableauDimNat =
            ∑ a : AddableRow mu,
              tableauDimNat (addAddableRowDiagram mu a) :=
          (sum_addableRows_eq_sum_upperCovers mu tableauDimNat).symm
        _ = ∑ _a : AddableRow mu, 1 := by
          apply Fintype.sum_congr
          intro a
          exact tableauDimNat_rank_one _
        _ = 1 := by simp [card_addableRows_rank_zero mu]
        _ = (0 + 1) * tableauDimNat mu := by
          simp
  | succ n ih =>
      calc
        (youngUpperCovers mu).sum tableauDimNat =
            (youngUpperCovers mu).sum (fun lam =>
              (youngLowerCovers lam).sum tableauDimNat) := by
          apply Finset.sum_congr rfl
          intro lam hlam
          exact tableauDimNat_eq_sum_lowerCovers lam
        _ = tableauDimNat mu +
            (youngLowerCovers mu).sum (fun kap =>
              (youngUpperCovers kap).sum tableauDimNat) := by
          exact youngLattice_up_down_sum mu tableauDimNat
        _ = tableauDimNat mu +
            (youngLowerCovers mu).sum (fun kap =>
              (n + 1) * tableauDimNat kap) := by
          apply congrArg (tableauDimNat mu + ·)
          apply Finset.sum_congr rfl
          intro kap hkap
          exact ih kap
        _ = tableauDimNat mu +
            (n + 1) * (youngLowerCovers mu).sum tableauDimNat := by
          rw [Finset.mul_sum]
        _ = tableauDimNat mu + (n + 1) * tableauDimNat mu := by
          rw [← tableauDimNat_eq_sum_lowerCovers mu]
        _ = (Nat.succ n + 1) * tableauDimNat mu := by
          simp [Nat.succ_eq_add_one, add_mul, add_comm]

/-- Double-counting one-box incidences exchanges lower-cover and upper-cover
summation. -/
theorem sum_lowerCovers_eq_sum_upperCovers {n : Nat}
    (f : YoungDiagram (n + 1) → YoungDiagram n → Nat) :
    (∑ lam : YoungDiagram (n + 1),
        (youngLowerCovers lam).sum (fun mu => f lam mu)) =
      ∑ mu : YoungDiagram n,
        (youngUpperCovers mu).sum (fun lam => f lam mu) := by
  classical
  simp only [youngLowerCovers, oneBoxChildrenSized, youngUpperCovers,
    Finset.sum_filter]
  rw [Finset.sum_comm]

/-- Sum of squared standard-tableau counts over all shapes of rank `n`. -/
def youngTableauSquareSum (n : Nat) : Nat :=
  ∑ lam : YoungDiagram n, tableauDimNat lam ^ 2

@[simp] theorem youngTableauSquareSum_zero :
    youngTableauSquareSum 0 = 1 := by
  unfold youngTableauSquareSum
  calc
    (∑ lam : YoungDiagram 0, tableauDimNat lam ^ 2) =
        ∑ _lam : YoungDiagram 0, 1 := by
      apply Fintype.sum_congr
      intro lam
      simp
    _ = 1 := by simp [card_youngDiagram_rank_zero]

theorem youngTableauSquareSum_succ (n : Nat) :
    youngTableauSquareSum (n + 1) =
      (n + 1) * youngTableauSquareSum n := by
  unfold youngTableauSquareSum
  calc
    (∑ lam : YoungDiagram (n + 1), tableauDimNat lam ^ 2) =
        ∑ lam : YoungDiagram (n + 1),
          tableauDimNat lam *
            (youngLowerCovers lam).sum tableauDimNat := by
      apply Fintype.sum_congr
      intro lam
      rw [← tableauDimNat_eq_sum_lowerCovers lam]
      simp [pow_two]
    _ = ∑ lam : YoungDiagram (n + 1),
          (youngLowerCovers lam).sum (fun mu =>
            tableauDimNat lam * tableauDimNat mu) := by
      apply Fintype.sum_congr
      intro lam
      rw [Finset.mul_sum]
    _ = ∑ mu : YoungDiagram n,
          (youngUpperCovers mu).sum (fun lam =>
            tableauDimNat lam * tableauDimNat mu) := by
      exact sum_lowerCovers_eq_sum_upperCovers
        (fun lam mu => tableauDimNat lam * tableauDimNat mu)
    _ = ∑ mu : YoungDiagram n,
          (youngUpperCovers mu).sum tableauDimNat * tableauDimNat mu := by
      apply Fintype.sum_congr
      intro mu
      rw [Finset.sum_mul]
    _ = ∑ mu : YoungDiagram n,
          ((n + 1) * tableauDimNat mu) * tableauDimNat mu := by
      apply Fintype.sum_congr
      intro mu
      rw [sum_tableauDimNat_upperCovers n mu]
    _ = ∑ mu : YoungDiagram n,
          (n + 1) * tableauDimNat mu ^ 2 := by
      apply Fintype.sum_congr
      intro mu
      simp [pow_two, mul_assoc]
    _ = (n + 1) * ∑ mu : YoungDiagram n,
          tableauDimNat mu ^ 2 := by
      rw [Finset.mul_sum]

/-- The tableau sum-of-squares identity, proved internally from the
differential Young-lattice recurrence. -/
theorem sum_tableauDimNat_sq_eq_factorial (n : Nat) :
    (∑ lam : YoungDiagram n, tableauDimNat lam ^ 2) = Nat.factorial n := by
  change youngTableauSquareSum n = Nat.factorial n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [youngTableauSquareSum_succ, ih, Nat.factorial_succ]

end AlgebraicLibrary
