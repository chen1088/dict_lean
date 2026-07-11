import DictatorshipTesting.Paper.S05_Int_TableauDimension

/-!
# Young-tableau square sums

This file develops the rank-generic Young-lattice combinatorics needed to prove
that the sum of the squared numbers of standard tableaux is a factorial.  The
first layer exposes one-box lower and upper covers and restates the existing
tableau-deletion recursion over natural numbers.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

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
  have hsum_subtype :
      (∑ mu : {mu : YoungDiagram n // mu ∈ youngLowerCovers lam},
        tableauDimNat mu.1) =
        (youngLowerCovers lam).sum (fun mu => tableauDimNat mu) := by
    rw [Finset.univ_eq_attach]
    exact Finset.sum_attach (youngLowerCovers lam) (fun mu => tableauDimNat mu)
  exact (Fintype.sum_equiv
    (removableRowsEquivOneBoxChildren lam)
    (fun r : RemovableRow lam =>
      tableauDimNat (removableRowToOneBoxChild lam r))
    (fun mu : {mu : YoungDiagram n // mu ∈ youngLowerCovers lam} =>
      tableauDimNat mu.1)
    (fun _ => rfl)).trans hsum_subtype

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

end DictatorshipTesting
