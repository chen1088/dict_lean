import DictatorshipTesting.Paper.Aux_YoungAdjacentEntries
import DictatorshipTesting.Paper.Aux_TableauDimension

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Aux_YoungAdjacentAction`
- `DictatorshipTesting.Paper.Aux_YoungMatchingOperators`
- `DictatorshipTesting.Paper.S05_Def5_04_TableauCoordinateSpace`
- `DictatorshipTesting.Paper.S05_Def5_05_ContentAndAdjacentOperators`
- `DictatorshipTesting.Paper.S05_Lem5_05_OneBoxDeletionIsUnitary`
-/


/-!
Elementary coordinate-space objects for the tableau-basis side of the rewritten
Section 5 proof.  This file deliberately stops before any Specht-module or
Schur-lemma assertions: the objects here are just finite functions on standard
Young tableaux, their coordinate basis, and the Euclidean dot product.
-/

noncomputable section

namespace DictatorshipTesting

open scoped BigOperators

local instance standardYoungTableauDecidableEq {n : Nat} {lam : YoungDiagram n} :
    DecidableEq (StandardYoungTableau lam) :=
  Classical.decEq _

/-- The real coordinate space with standard tableaux of shape `lam` as basis. -/
abbrev TableauSpace {n : Nat} (lam : YoungDiagram n) :=
  StandardYoungTableau lam -> ℝ

/-- The coordinate basis vector indexed by one standard tableau. -/
def tableauBasisVec {n : Nat} {lam : YoungDiagram n}
    (T : StandardYoungTableau lam) : TableauSpace lam :=
  fun S => if S = T then 1 else 0

/-- The Euclidean dot product in the tableau coordinate basis. -/
def tableauInner {n : Nat} {lam : YoungDiagram n}
    (f g : TableauSpace lam) : ℝ :=
  ∑ T : StandardYoungTableau lam, f T * g T

@[simp] theorem tableauBasisVec_self {n : Nat} {lam : YoungDiagram n}
    (T : StandardYoungTableau lam) :
    tableauBasisVec T T = 1 := by
  simp [tableauBasisVec]

theorem tableauBasisVec_ne {n : Nat} {lam : YoungDiagram n}
    {S T : StandardYoungTableau lam} (h : S ≠ T) :
    tableauBasisVec T S = 0 := by
  simp [tableauBasisVec, h]

theorem tableauBasis_expansion {n : Nat} {lam : YoungDiagram n}
    (f : TableauSpace lam) :
    f = fun S => ∑ T : StandardYoungTableau lam, f T * tableauBasisVec T S := by
  classical
  funext S
  rw [Fintype.sum_eq_single S]
  · simp [tableauBasisVec]
  · intro T hT
    rw [tableauBasisVec_ne (fun h => hT h.symm)]
    ring

@[simp] theorem tableauInner_basis_basis_self {n : Nat} {lam : YoungDiagram n}
    (T : StandardYoungTableau lam) :
    tableauInner (tableauBasisVec T) (tableauBasisVec T) = 1 := by
  classical
  rw [tableauInner]
  rw [Fintype.sum_eq_single T]
  · simp [tableauBasisVec]
  · intro S hS
    simp [tableauBasisVec, hS]

theorem tableauInner_basis_basis_ne {n : Nat} {lam : YoungDiagram n}
    {S T : StandardYoungTableau lam} (h : S ≠ T) :
    tableauInner (tableauBasisVec S) (tableauBasisVec T) = 0 := by
  classical
  rw [tableauInner]
  apply Finset.sum_eq_zero
  intro U _
  by_cases hUS : U = S
  · subst U
    simp [tableauBasisVec, h]
  · simp [tableauBasisVec, hUS]

theorem tableauInner_basis_basis_eq_ite {n : Nat} {lam : YoungDiagram n}
    (S T : StandardYoungTableau lam) :
    tableauInner (tableauBasisVec S) (tableauBasisVec T) =
      if S = T then 1 else 0 := by
  by_cases h : S = T
  · subst T
    simp
  · simp [h, tableauInner_basis_basis_ne h]

theorem tableauInner_right_basis {n : Nat} {lam : YoungDiagram n}
    (f : TableauSpace lam) (T : StandardYoungTableau lam) :
    tableauInner f (tableauBasisVec T) = f T := by
  classical
  rw [tableauInner]
  rw [Fintype.sum_eq_single T]
  · simp [tableauBasisVec]
  · intro S hS
    simp [tableauBasisVec, hS]

theorem tableauInner_left_basis {n : Nat} {lam : YoungDiagram n}
    (T : StandardYoungTableau lam) (f : TableauSpace lam) :
    tableauInner (tableauBasisVec T) f = f T := by
  classical
  rw [tableauInner]
  rw [Fintype.sum_eq_single T]
  · simp [tableauBasisVec]
  · intro S hS
    simp [tableauBasisVec, hS]

/-- The adjacent entries indexed by `a` occupy a common row. -/
def adjacentSameRow {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) : Prop :=
  YoungCell.row (adjacentLoCell T a) =
    YoungCell.row (adjacentHiCell T a)

/-- The adjacent entries indexed by `a` occupy a common column. -/
def adjacentSameCol {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) : Prop :=
  YoungCell.col (adjacentLoCell T a) =
    YoungCell.col (adjacentHiCell T a)

local instance adjacentSameRowDecidable {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) :
    Decidable (adjacentSameRow T a) := by
  unfold adjacentSameRow
  infer_instance

local instance adjacentSameColDecidable {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) :
    Decidable (adjacentSameCol T a) := by
  unfold adjacentSameCol
  infer_instance

/-- Axial distance between the cells of adjacent entries `a` and `a+1`. -/
def adjacentAxialDistance {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) : Int :=
  entryContent T (adjacentEntryHi a) -
    entryContent T (adjacentEntryLo a)

theorem adjacentAxialDistance_sameRow {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow : adjacentSameRow T a) :
    adjacentAxialDistance T a = 1 := by
  have hcontent :
      entryContent T (adjacentEntryHi a) =
        entryContent T (adjacentEntryLo a) + 1 := by
    simpa [entryContent, adjacentHiCell, adjacentLoCell, adjacentSameRow] using
      adjacent_content_hi_eq_lo_add_one_of_sameRow T a hrow
  unfold adjacentAxialDistance
  omega

theorem adjacentAxialDistance_sameCol {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol : adjacentSameCol T a) :
    adjacentAxialDistance T a = -1 := by
  have hcontent :
      entryContent T (adjacentEntryHi a) =
        entryContent T (adjacentEntryLo a) - 1 := by
    simpa [entryContent, adjacentHiCell, adjacentLoCell, adjacentSameCol] using
      adjacent_content_hi_eq_lo_sub_one_of_sameCol T a hcol
  unfold adjacentAxialDistance
  omega

theorem adjacentAxialDistance_swap_neg {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    adjacentAxialDistance (adjacentSwapTableau T a hrow_ne hcol_ne) a =
      - adjacentAxialDistance T a := by
  unfold adjacentAxialDistance
  rw [adjacentSwapTableau_entryContent_hi,
    adjacentSwapTableau_entryContent_lo]
  omega

theorem adjacentAxialDistance_after_disjoint_swap_eq {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hdisj : adjacentIndexDisjoint a b)
    (hrow_b :
      YoungCell.row (adjacentLoCell T b) ≠
        YoungCell.row (adjacentHiCell T b))
    (hcol_b :
      YoungCell.col (adjacentLoCell T b) ≠
        YoungCell.col (adjacentHiCell T b)) :
    adjacentAxialDistance (adjacentSwapTableau T b hrow_b hcol_b) a =
      adjacentAxialDistance T a := by
  unfold adjacentAxialDistance
  rw [adjacentSwapTableau_entryContent_of_ne_lo_hi T b hrow_b hcol_b
      (adjacentEntryHi_ne_lo_of_disjoint_indices a b hdisj)
      (adjacentEntryHi_ne_hi_of_disjoint_indices a b hdisj),
    adjacentSwapTableau_entryContent_of_ne_lo_hi T b hrow_b hcol_b
      (adjacentEntryLo_ne_lo_of_disjoint_indices a b hdisj)
      (adjacentEntryLo_ne_hi_of_disjoint_indices a b hdisj)]

theorem adjacentAxialDistance_after_left_swap_of_succ {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hsucc : (b : Nat) = (a : Nat) + 1)
    (hrow_a :
      ¬ adjacentSameRow T a)
    (hcol_a :
      ¬ adjacentSameCol T a) :
    adjacentAxialDistance (adjacentSwapTableau T a hrow_a hcol_a) b =
      adjacentAxialDistance T a + adjacentAxialDistance T b := by
  have hhi_lo : adjacentEntryHi a = adjacentEntryLo b :=
    adjacentEntryHi_eq_lo_of_succ a b hsucc
  have hhi_b_ne_lo_a : adjacentEntryHi b ≠ adjacentEntryLo a := by
    intro h
    have hv := congrArg Fin.val h
    simp [adjacentEntryHi, adjacentEntryLo, hsucc] at hv
    omega
  have hhi_b_ne_hi_a : adjacentEntryHi b ≠ adjacentEntryHi a := by
    intro h
    have hv := congrArg Fin.val h
    simp [adjacentEntryHi, hsucc] at hv
  unfold adjacentAxialDistance
  rw [adjacentSwapTableau_entryContent_of_ne_lo_hi T a hrow_a hcol_a
      hhi_b_ne_lo_a hhi_b_ne_hi_a]
  rw [show entryContent (adjacentSwapTableau T a hrow_a hcol_a)
        (adjacentEntryLo b) =
        entryContent T (adjacentEntryLo a) by
      rw [← hhi_lo]
      exact adjacentSwapTableau_entryContent_hi T a hrow_a hcol_a]
  rw [hhi_lo]
  ring

theorem adjacentAxialDistance_after_right_swap_of_succ {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hsucc : (b : Nat) = (a : Nat) + 1)
    (hrow_b :
      ¬ adjacentSameRow T b)
    (hcol_b :
      ¬ adjacentSameCol T b) :
    adjacentAxialDistance (adjacentSwapTableau T b hrow_b hcol_b) a =
      adjacentAxialDistance T a + adjacentAxialDistance T b := by
  have hhi_lo : adjacentEntryHi a = adjacentEntryLo b :=
    adjacentEntryHi_eq_lo_of_succ a b hsucc
  have hlo_a_ne_lo_b : adjacentEntryLo a ≠ adjacentEntryLo b := by
    intro h
    have hv := congrArg Fin.val h
    simp [adjacentEntryLo, hsucc] at hv
  have hlo_a_ne_hi_b : adjacentEntryLo a ≠ adjacentEntryHi b := by
    intro h
    have hv := congrArg Fin.val h
    simp [adjacentEntryLo, adjacentEntryHi, hsucc] at hv
    omega
  unfold adjacentAxialDistance
  rw [show entryContent (adjacentSwapTableau T b hrow_b hcol_b)
        (adjacentEntryHi a) =
        entryContent T (adjacentEntryHi b) by
      rw [hhi_lo]
      exact adjacentSwapTableau_entryContent_lo T b hrow_b hcol_b]
  rw [adjacentSwapTableau_entryContent_of_ne_lo_hi T b hrow_b hcol_b
      hlo_a_ne_lo_b hlo_a_ne_hi_b]
  rw [hhi_lo]
  ring

theorem adjacentAxialDistance_after_left_right_swap_of_succ {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hsucc : (b : Nat) = (a : Nat) + 1)
    (hrow_a : ¬ adjacentSameRow T a)
    (hcol_a : ¬ adjacentSameCol T a)
    (hrow_b_after_a :
      ¬ adjacentSameRow (adjacentSwapTableau T a hrow_a hcol_a) b)
    (hcol_b_after_a :
      ¬ adjacentSameCol (adjacentSwapTableau T a hrow_a hcol_a) b) :
    adjacentAxialDistance
        (adjacentSwapTableau
          (adjacentSwapTableau T a hrow_a hcol_a) b
          hrow_b_after_a hcol_b_after_a) a =
      adjacentAxialDistance T b := by
  let Ta := adjacentSwapTableau T a hrow_a hcol_a
  have hright :
      adjacentAxialDistance
          (adjacentSwapTableau Ta b hrow_b_after_a hcol_b_after_a) a =
        adjacentAxialDistance Ta a + adjacentAxialDistance Ta b := by
    exact adjacentAxialDistance_after_right_swap_of_succ
      Ta a b hsucc hrow_b_after_a hcol_b_after_a
  have hswap :
      adjacentAxialDistance Ta a = - adjacentAxialDistance T a := by
    simpa [Ta] using adjacentAxialDistance_swap_neg T a hrow_a hcol_a
  have hneighbor :
      adjacentAxialDistance Ta b =
        adjacentAxialDistance T a + adjacentAxialDistance T b := by
    simpa [Ta] using
      adjacentAxialDistance_after_left_swap_of_succ T a b hsucc hrow_a hcol_a
  rw [hright, hswap, hneighbor]
  omega

theorem adjacentAxialDistance_after_right_left_swap_of_succ {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hsucc : (b : Nat) = (a : Nat) + 1)
    (hrow_b : ¬ adjacentSameRow T b)
    (hcol_b : ¬ adjacentSameCol T b)
    (hrow_a_after_b :
      ¬ adjacentSameRow (adjacentSwapTableau T b hrow_b hcol_b) a)
    (hcol_a_after_b :
      ¬ adjacentSameCol (adjacentSwapTableau T b hrow_b hcol_b) a) :
    adjacentAxialDistance
        (adjacentSwapTableau
          (adjacentSwapTableau T b hrow_b hcol_b) a
          hrow_a_after_b hcol_a_after_b) b =
      adjacentAxialDistance T a := by
  let Tb := adjacentSwapTableau T b hrow_b hcol_b
  have hleft :
      adjacentAxialDistance
          (adjacentSwapTableau Tb a hrow_a_after_b hcol_a_after_b) b =
        adjacentAxialDistance Tb a + adjacentAxialDistance Tb b := by
    exact adjacentAxialDistance_after_left_swap_of_succ
      Tb a b hsucc hrow_a_after_b hcol_a_after_b
  have hneighbor :
      adjacentAxialDistance Tb a =
        adjacentAxialDistance T a + adjacentAxialDistance T b := by
    simpa [Tb] using
      adjacentAxialDistance_after_right_swap_of_succ T a b hsucc hrow_b hcol_b
  have hswap :
      adjacentAxialDistance Tb b = - adjacentAxialDistance T b := by
    simpa [Tb] using adjacentAxialDistance_swap_neg T b hrow_b hcol_b
  rw [hleft, hneighbor, hswap]
  omega

theorem adjacentAxialDistance_ne_zero_of_swappable {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (_hcol_ne : ¬ adjacentSameCol T a) :
    adjacentAxialDistance T a ≠ 0 := by
  intro hzero
  let lo := adjacentLoCell T a
  let hi := adjacentHiCell T a
  have hrow_ne_raw : YoungCell.row lo ≠ YoungCell.row hi := by
    simpa [lo, hi, adjacentSameRow] using hrow_ne
  have hcontent_entry :
      entryContent T (adjacentEntryHi a) =
        entryContent T (adjacentEntryLo a) := by
    unfold adjacentAxialDistance at hzero
    omega
  have hcontent : YoungCell.content hi = YoungCell.content lo := by
    simpa [entryContent, adjacentHiCell, adjacentLoCell, lo, hi]
      using hcontent_entry
  rcases lt_or_gt_of_ne hrow_ne_raw with hrow_lt | hrow_lt
  · have hcol_lt : YoungCell.col lo < YoungCell.col hi := by
      unfold YoungCell.content at hcontent
      omega
    have hhi_box : YoungCell.col hi < youngRow lam (YoungCell.row hi) := by
      simpa [YoungCell.toNatPair, IsYoungBox] using YoungCell.isYoungBox hi
    have hrow_le :
        youngRow lam (YoungCell.row hi) <=
          youngRow lam (YoungCell.row lo) :=
      youngRow_le_of_le lam (Nat.le_of_lt hrow_lt)
    have hmid_cell :
        YoungCell.col hi < youngRow lam (YoungCell.row lo) := by
      omega
    let mid : YoungCell lam :=
      youngCellOfNat lam (YoungCell.row lo) (YoungCell.col hi) hmid_cell
    have hlo_mid : T.entry lo < T.entry mid := by
      apply T.row_strict
      · simp [mid, youngCellOfNat_row]
      · simp [mid, youngCellOfNat_col, hcol_lt]
    have hmid_hi : T.entry mid < T.entry hi := by
      apply T.col_strict
      · simp [mid, youngCellOfNat_col]
      · simp [mid, youngCellOfNat_row, hrow_lt]
    have hlo_mid_val : (T.entry lo : Nat) < (T.entry mid : Nat) := hlo_mid
    have hmid_hi_val : (T.entry mid : Nat) < (T.entry hi : Nat) := hmid_hi
    have hlo_val : (T.entry lo : Nat) = (a : Nat) := by
      rw [show T.entry lo = adjacentEntryLo a by
        simpa [lo] using entry_adjacentLoCell T a]
      rfl
    have hhi_val : (T.entry hi : Nat) = (a : Nat) + 1 := by
      rw [show T.entry hi = adjacentEntryHi a by
        simpa [hi] using entry_adjacentHiCell T a]
      rfl
    omega
  · have hcol_lt : YoungCell.col hi < YoungCell.col lo := by
      unfold YoungCell.content at hcontent
      omega
    have hlo_box : YoungCell.col lo < youngRow lam (YoungCell.row lo) := by
      simpa [YoungCell.toNatPair, IsYoungBox] using YoungCell.isYoungBox lo
    have hrow_le :
        youngRow lam (YoungCell.row lo) <=
          youngRow lam (YoungCell.row hi) :=
      youngRow_le_of_le lam (Nat.le_of_lt hrow_lt)
    have hmid_cell :
        YoungCell.col lo < youngRow lam (YoungCell.row hi) := by
      omega
    let mid : YoungCell lam :=
      youngCellOfNat lam (YoungCell.row hi) (YoungCell.col lo) hmid_cell
    have hhi_mid : T.entry hi < T.entry mid := by
      apply T.row_strict
      · simp [mid, youngCellOfNat_row]
      · simp [mid, youngCellOfNat_col, hcol_lt]
    have hmid_lo : T.entry mid < T.entry lo := by
      apply T.col_strict
      · simp [mid, youngCellOfNat_col]
      · simp [mid, youngCellOfNat_row, hrow_lt]
    have hhi_mid_val : (T.entry hi : Nat) < (T.entry mid : Nat) := hhi_mid
    have hmid_lo_val : (T.entry mid : Nat) < (T.entry lo : Nat) := hmid_lo
    have hlo_val : (T.entry lo : Nat) = (a : Nat) := by
      rw [show T.entry lo = adjacentEntryLo a by
        simpa [lo] using entry_adjacentLoCell T a]
      rfl
    have hhi_val : (T.entry hi : Nat) = (a : Nat) + 1 := by
      rw [show T.entry hi = adjacentEntryHi a by
        simpa [hi] using entry_adjacentHiCell T a]
      rfl
    omega

theorem adjacentAxialDistance_ne_one_of_swappable {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    adjacentAxialDistance T a ≠ 1 := by
  intro hone
  let lo := adjacentLoCell T a
  let hi := adjacentHiCell T a
  have hrow_ne_raw : YoungCell.row lo ≠ YoungCell.row hi := by
    simpa [lo, hi, adjacentSameRow] using hrow_ne
  have hcol_ne_raw : YoungCell.col lo ≠ YoungCell.col hi := by
    simpa [lo, hi, adjacentSameCol] using hcol_ne
  have hcontent_entry :
      entryContent T (adjacentEntryHi a) =
        entryContent T (adjacentEntryLo a) + 1 := by
    unfold adjacentAxialDistance at hone
    omega
  have hcontent : YoungCell.content hi = YoungCell.content lo + 1 := by
    simpa [entryContent, adjacentHiCell, adjacentLoCell, lo, hi]
      using hcontent_entry
  rcases lt_or_gt_of_ne hrow_ne_raw with hrow_lt | hrow_lt
  · have hcol_lt : YoungCell.col lo < YoungCell.col hi := by
      unfold YoungCell.content at hcontent
      omega
    have hhi_box : YoungCell.col hi < youngRow lam (YoungCell.row hi) := by
      simpa [YoungCell.toNatPair, IsYoungBox] using YoungCell.isYoungBox hi
    have hrow_le :
        youngRow lam (YoungCell.row hi) <=
          youngRow lam (YoungCell.row lo) :=
      youngRow_le_of_le lam (Nat.le_of_lt hrow_lt)
    have hmid_cell :
        YoungCell.col hi < youngRow lam (YoungCell.row lo) := by
      omega
    let mid : YoungCell lam :=
      youngCellOfNat lam (YoungCell.row lo) (YoungCell.col hi) hmid_cell
    have hlo_mid : T.entry lo < T.entry mid := by
      apply T.row_strict
      · simp [mid, youngCellOfNat_row]
      · simp [mid, youngCellOfNat_col, hcol_lt]
    have hmid_hi : T.entry mid < T.entry hi := by
      apply T.col_strict
      · simp [mid, youngCellOfNat_col]
      · simp [mid, youngCellOfNat_row, hrow_lt]
    have hlo_mid_val : (T.entry lo : Nat) < (T.entry mid : Nat) := hlo_mid
    have hmid_hi_val : (T.entry mid : Nat) < (T.entry hi : Nat) := hmid_hi
    have hlo_val : (T.entry lo : Nat) = (a : Nat) := by
      rw [show T.entry lo = adjacentEntryLo a by
        simpa [lo] using entry_adjacentLoCell T a]
      rfl
    have hhi_val : (T.entry hi : Nat) = (a : Nat) + 1 := by
      rw [show T.entry hi = adjacentEntryHi a by
        simpa [hi] using entry_adjacentHiCell T a]
      rfl
    omega
  · have hcol_lt : YoungCell.col hi < YoungCell.col lo := by
      unfold YoungCell.content at hcontent
      omega
    have hlo_box : YoungCell.col lo < youngRow lam (YoungCell.row lo) := by
      simpa [YoungCell.toNatPair, IsYoungBox] using YoungCell.isYoungBox lo
    have hrow_le :
        youngRow lam (YoungCell.row lo) <=
          youngRow lam (YoungCell.row hi) :=
      youngRow_le_of_le lam (Nat.le_of_lt hrow_lt)
    have hmid_cell :
        YoungCell.col lo < youngRow lam (YoungCell.row hi) := by
      omega
    let mid : YoungCell lam :=
      youngCellOfNat lam (YoungCell.row hi) (YoungCell.col lo) hmid_cell
    have hhi_mid : T.entry hi < T.entry mid := by
      apply T.row_strict
      · simp [mid, youngCellOfNat_row]
      · simp [mid, youngCellOfNat_col, hcol_lt]
    have hmid_lo : T.entry mid < T.entry lo := by
      apply T.col_strict
      · simp [mid, youngCellOfNat_col]
      · simp [mid, youngCellOfNat_row, hrow_lt]
    have hhi_mid_val : (T.entry hi : Nat) < (T.entry mid : Nat) := hhi_mid
    have hmid_lo_val : (T.entry mid : Nat) < (T.entry lo : Nat) := hmid_lo
    have hlo_val : (T.entry lo : Nat) = (a : Nat) := by
      rw [show T.entry lo = adjacentEntryLo a by
        simpa [lo] using entry_adjacentLoCell T a]
      rfl
    have hhi_val : (T.entry hi : Nat) = (a : Nat) + 1 := by
      rw [show T.entry hi = adjacentEntryHi a by
        simpa [hi] using entry_adjacentHiCell T a]
      rfl
    omega

theorem adjacentAxialDistance_ne_neg_one_of_swappable {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    adjacentAxialDistance T a ≠ -1 := by
  intro hneg
  let lo := adjacentLoCell T a
  let hi := adjacentHiCell T a
  have hrow_ne_raw : YoungCell.row lo ≠ YoungCell.row hi := by
    simpa [lo, hi, adjacentSameRow] using hrow_ne
  have hcol_ne_raw : YoungCell.col lo ≠ YoungCell.col hi := by
    simpa [lo, hi, adjacentSameCol] using hcol_ne
  have hcontent_entry :
      entryContent T (adjacentEntryHi a) =
        entryContent T (adjacentEntryLo a) - 1 := by
    unfold adjacentAxialDistance at hneg
    omega
  have hcontent : YoungCell.content hi = YoungCell.content lo - 1 := by
    simpa [entryContent, adjacentHiCell, adjacentLoCell, lo, hi]
      using hcontent_entry
  rcases lt_or_gt_of_ne hcol_ne_raw with hcol_lt | hcol_lt
  · have hrow_lt : YoungCell.row lo < YoungCell.row hi := by
      unfold YoungCell.content at hcontent
      omega
    have hhi_box : YoungCell.col hi < youngRow lam (YoungCell.row hi) := by
      simpa [YoungCell.toNatPair, IsYoungBox] using YoungCell.isYoungBox hi
    have hmid_cell :
        YoungCell.col lo < youngRow lam (YoungCell.row hi) := by
      omega
    let mid : YoungCell lam :=
      youngCellOfNat lam (YoungCell.row hi) (YoungCell.col lo) hmid_cell
    have hlo_mid : T.entry lo < T.entry mid := by
      apply T.col_strict
      · simp [mid, youngCellOfNat_col]
      · simp [mid, youngCellOfNat_row, hrow_lt]
    have hmid_hi : T.entry mid < T.entry hi := by
      apply T.row_strict
      · simp [mid, youngCellOfNat_row]
      · simp [mid, youngCellOfNat_col, hcol_lt]
    have hlo_mid_val : (T.entry lo : Nat) < (T.entry mid : Nat) := hlo_mid
    have hmid_hi_val : (T.entry mid : Nat) < (T.entry hi : Nat) := hmid_hi
    have hlo_val : (T.entry lo : Nat) = (a : Nat) := by
      rw [show T.entry lo = adjacentEntryLo a by
        simpa [lo] using entry_adjacentLoCell T a]
      rfl
    have hhi_val : (T.entry hi : Nat) = (a : Nat) + 1 := by
      rw [show T.entry hi = adjacentEntryHi a by
        simpa [hi] using entry_adjacentHiCell T a]
      rfl
    omega
  · have hrow_lt : YoungCell.row hi < YoungCell.row lo := by
      unfold YoungCell.content at hcontent
      omega
    have hlo_box : YoungCell.col lo < youngRow lam (YoungCell.row lo) := by
      simpa [YoungCell.toNatPair, IsYoungBox] using YoungCell.isYoungBox lo
    have hrow_le :
        youngRow lam (YoungCell.row lo) <=
          youngRow lam (YoungCell.row hi) :=
      youngRow_le_of_le lam (Nat.le_of_lt hrow_lt)
    have hmid_cell :
        YoungCell.col lo < youngRow lam (YoungCell.row hi) := by
      omega
    let mid : YoungCell lam :=
      youngCellOfNat lam (YoungCell.row hi) (YoungCell.col lo) hmid_cell
    have hhi_mid : T.entry hi < T.entry mid := by
      apply T.row_strict
      · simp [mid, youngCellOfNat_row]
      · simp [mid, youngCellOfNat_col, hcol_lt]
    have hmid_lo : T.entry mid < T.entry lo := by
      apply T.col_strict
      · simp [mid, youngCellOfNat_col]
      · simp [mid, youngCellOfNat_row, hrow_lt]
    have hhi_mid_val : (T.entry hi : Nat) < (T.entry mid : Nat) := hhi_mid
    have hmid_lo_val : (T.entry mid : Nat) < (T.entry lo : Nat) := hmid_lo
    have hlo_val : (T.entry lo : Nat) = (a : Nat) := by
      rw [show T.entry lo = adjacentEntryLo a by
        simpa [lo] using entry_adjacentLoCell T a]
      rfl
    have hhi_val : (T.entry hi : Nat) = (a : Nat) + 1 := by
      rw [show T.entry hi = adjacentEntryHi a by
        simpa [hi] using entry_adjacentHiCell T a]
      rfl
    omega

theorem adjacentSameRow_of_axialDistance_eq_one {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (h : adjacentAxialDistance T a = 1) :
    adjacentSameRow T a := by
  by_cases hrow : adjacentSameRow T a
  · exact hrow
  · by_cases hcol : adjacentSameCol T a
    · have hneg := adjacentAxialDistance_sameCol T a hcol
      omega
    · exact False.elim
        (adjacentAxialDistance_ne_one_of_swappable T a hrow hcol h)

theorem adjacentSameCol_of_axialDistance_eq_neg_one {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (h : adjacentAxialDistance T a = -1) :
    adjacentSameCol T a := by
  by_cases hcol : adjacentSameCol T a
  · exact hcol
  · by_cases hrow : adjacentSameRow T a
    · have hone := adjacentAxialDistance_sameRow T a hrow
      omega
    · exact False.elim
        (adjacentAxialDistance_ne_neg_one_of_swappable T a hrow hcol h)

/-- Diagonal coefficient in Young's adjacent-transposition formula. -/
noncomputable def youngAdjacentDiagCoeff {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) : ℝ :=
  (adjacentAxialDistance T a : ℝ)⁻¹

/-- Off-diagonal coefficient in Young's adjacent-transposition formula. -/
noncomputable def youngAdjacentOffCoeff {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) : ℝ :=
  Real.sqrt (1 - youngAdjacentDiagCoeff T a ^ 2)

theorem youngAdjacentDiagCoeff_sameRow {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow : adjacentSameRow T a) :
    youngAdjacentDiagCoeff T a = 1 := by
  rw [youngAdjacentDiagCoeff, adjacentAxialDistance_sameRow T a hrow]
  norm_num

theorem youngAdjacentDiagCoeff_sameCol {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol : adjacentSameCol T a) :
    youngAdjacentDiagCoeff T a = -1 := by
  rw [youngAdjacentDiagCoeff, adjacentAxialDistance_sameCol T a hcol]
  norm_num

theorem youngAdjacentOffCoeff_sameRow {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow : adjacentSameRow T a) :
    youngAdjacentOffCoeff T a = 0 := by
  rw [youngAdjacentOffCoeff, youngAdjacentDiagCoeff_sameRow T a hrow]
  norm_num

theorem youngAdjacentOffCoeff_sameCol {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol : adjacentSameCol T a) :
    youngAdjacentOffCoeff T a = 0 := by
  rw [youngAdjacentOffCoeff, youngAdjacentDiagCoeff_sameCol T a hcol]
  norm_num

theorem youngAdjacentDiagCoeff_after_disjoint_swap_eq {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hdisj : adjacentIndexDisjoint a b)
    (hrow_b :
      YoungCell.row (adjacentLoCell T b) ≠
        YoungCell.row (adjacentHiCell T b))
    (hcol_b :
      YoungCell.col (adjacentLoCell T b) ≠
        YoungCell.col (adjacentHiCell T b)) :
    youngAdjacentDiagCoeff (adjacentSwapTableau T b hrow_b hcol_b) a =
      youngAdjacentDiagCoeff T a := by
  rw [youngAdjacentDiagCoeff, youngAdjacentDiagCoeff,
    adjacentAxialDistance_after_disjoint_swap_eq T a b hdisj hrow_b hcol_b]

theorem youngAdjacentDiagCoeff_after_left_swap_of_succ {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hsucc : (b : Nat) = (a : Nat) + 1)
    (hrow_a : ¬ adjacentSameRow T a)
    (hcol_a : ¬ adjacentSameCol T a) :
    youngAdjacentDiagCoeff (adjacentSwapTableau T a hrow_a hcol_a) b =
      ((adjacentAxialDistance T a + adjacentAxialDistance T b : Int) : ℝ)⁻¹ := by
  rw [youngAdjacentDiagCoeff,
    adjacentAxialDistance_after_left_swap_of_succ T a b hsucc hrow_a hcol_a]

theorem youngAdjacentDiagCoeff_after_right_swap_of_succ {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hsucc : (b : Nat) = (a : Nat) + 1)
    (hrow_b : ¬ adjacentSameRow T b)
    (hcol_b : ¬ adjacentSameCol T b) :
    youngAdjacentDiagCoeff (adjacentSwapTableau T b hrow_b hcol_b) a =
      ((adjacentAxialDistance T a + adjacentAxialDistance T b : Int) : ℝ)⁻¹ := by
  rw [youngAdjacentDiagCoeff,
    adjacentAxialDistance_after_right_swap_of_succ T a b hsucc hrow_b hcol_b]

theorem youngAdjacentDiagCoeff_after_left_swap_eq_after_right_swap_of_succ
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hsucc : (b : Nat) = (a : Nat) + 1)
    (hrow_a : ¬ adjacentSameRow T a)
    (hcol_a : ¬ adjacentSameCol T a)
    (hrow_b : ¬ adjacentSameRow T b)
    (hcol_b : ¬ adjacentSameCol T b) :
    youngAdjacentDiagCoeff (adjacentSwapTableau T a hrow_a hcol_a) b =
      youngAdjacentDiagCoeff (adjacentSwapTableau T b hrow_b hcol_b) a := by
  rw [youngAdjacentDiagCoeff_after_left_swap_of_succ T a b hsucc hrow_a hcol_a,
    youngAdjacentDiagCoeff_after_right_swap_of_succ T a b hsucc hrow_b hcol_b]

theorem youngAdjacentOffCoeff_after_left_swap_eq_after_right_swap_of_succ
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hsucc : (b : Nat) = (a : Nat) + 1)
    (hrow_a : ¬ adjacentSameRow T a)
    (hcol_a : ¬ adjacentSameCol T a)
    (hrow_b : ¬ adjacentSameRow T b)
    (hcol_b : ¬ adjacentSameCol T b) :
    youngAdjacentOffCoeff (adjacentSwapTableau T a hrow_a hcol_a) b =
      youngAdjacentOffCoeff (adjacentSwapTableau T b hrow_b hcol_b) a := by
  rw [youngAdjacentOffCoeff, youngAdjacentOffCoeff,
    youngAdjacentDiagCoeff_after_left_swap_eq_after_right_swap_of_succ
      T a b hsucc hrow_a hcol_a hrow_b hcol_b]

theorem youngAdjacentDiagCoeff_after_left_right_swap_of_succ {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hsucc : (b : Nat) = (a : Nat) + 1)
    (hrow_a : ¬ adjacentSameRow T a)
    (hcol_a : ¬ adjacentSameCol T a)
    (hrow_b_after_a :
      ¬ adjacentSameRow (adjacentSwapTableau T a hrow_a hcol_a) b)
    (hcol_b_after_a :
      ¬ adjacentSameCol (adjacentSwapTableau T a hrow_a hcol_a) b) :
    youngAdjacentDiagCoeff
        (adjacentSwapTableau
          (adjacentSwapTableau T a hrow_a hcol_a) b
          hrow_b_after_a hcol_b_after_a) a =
      youngAdjacentDiagCoeff T b := by
  rw [youngAdjacentDiagCoeff, youngAdjacentDiagCoeff,
    adjacentAxialDistance_after_left_right_swap_of_succ
      T a b hsucc hrow_a hcol_a hrow_b_after_a hcol_b_after_a]

theorem youngAdjacentOffCoeff_after_left_right_swap_of_succ {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hsucc : (b : Nat) = (a : Nat) + 1)
    (hrow_a : ¬ adjacentSameRow T a)
    (hcol_a : ¬ adjacentSameCol T a)
    (hrow_b_after_a :
      ¬ adjacentSameRow (adjacentSwapTableau T a hrow_a hcol_a) b)
    (hcol_b_after_a :
      ¬ adjacentSameCol (adjacentSwapTableau T a hrow_a hcol_a) b) :
    youngAdjacentOffCoeff
        (adjacentSwapTableau
          (adjacentSwapTableau T a hrow_a hcol_a) b
          hrow_b_after_a hcol_b_after_a) a =
      youngAdjacentOffCoeff T b := by
  rw [youngAdjacentOffCoeff, youngAdjacentOffCoeff,
    youngAdjacentDiagCoeff_after_left_right_swap_of_succ
      T a b hsucc hrow_a hcol_a hrow_b_after_a hcol_b_after_a]

theorem youngAdjacentDiagCoeff_after_right_left_swap_of_succ {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hsucc : (b : Nat) = (a : Nat) + 1)
    (hrow_b : ¬ adjacentSameRow T b)
    (hcol_b : ¬ adjacentSameCol T b)
    (hrow_a_after_b :
      ¬ adjacentSameRow (adjacentSwapTableau T b hrow_b hcol_b) a)
    (hcol_a_after_b :
      ¬ adjacentSameCol (adjacentSwapTableau T b hrow_b hcol_b) a) :
    youngAdjacentDiagCoeff
        (adjacentSwapTableau
          (adjacentSwapTableau T b hrow_b hcol_b) a
          hrow_a_after_b hcol_a_after_b) b =
      youngAdjacentDiagCoeff T a := by
  rw [youngAdjacentDiagCoeff, youngAdjacentDiagCoeff,
    adjacentAxialDistance_after_right_left_swap_of_succ
      T a b hsucc hrow_b hcol_b hrow_a_after_b hcol_a_after_b]

theorem youngAdjacentOffCoeff_after_right_left_swap_of_succ {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hsucc : (b : Nat) = (a : Nat) + 1)
    (hrow_b : ¬ adjacentSameRow T b)
    (hcol_b : ¬ adjacentSameCol T b)
    (hrow_a_after_b :
      ¬ adjacentSameRow (adjacentSwapTableau T b hrow_b hcol_b) a)
    (hcol_a_after_b :
      ¬ adjacentSameCol (adjacentSwapTableau T b hrow_b hcol_b) a) :
    youngAdjacentOffCoeff
        (adjacentSwapTableau
          (adjacentSwapTableau T b hrow_b hcol_b) a
          hrow_a_after_b hcol_a_after_b) b =
      youngAdjacentOffCoeff T a := by
  rw [youngAdjacentOffCoeff, youngAdjacentOffCoeff,
    youngAdjacentDiagCoeff_after_right_left_swap_of_succ
      T a b hsucc hrow_b hcol_b hrow_a_after_b hcol_a_after_b]

theorem inv_braid_left_identity {x y z : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hz0 : z ≠ 0)
    (hsum : z = x + y) :
    x⁻¹ * (y⁻¹ - z⁻¹) = y⁻¹ * z⁻¹ := by
  subst z
  field_simp [hx, hy, hz0]
  ring

theorem inv_braid_right_identity {x y z : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hz0 : z ≠ 0)
    (hsum : z = x + y) :
    y⁻¹ * (x⁻¹ - z⁻¹) = x⁻¹ * z⁻¹ := by
  subst z
  field_simp [hx, hy, hz0]
  ring

theorem inv_sq_braid_diag_identity {x y z : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hz0 : z ≠ 0)
    (hsum : z = x + y) :
    x⁻¹ ^ 2 * y⁻¹ + (1 - x⁻¹ ^ 2) * z⁻¹ =
      y⁻¹ ^ 2 * x⁻¹ + (1 - y⁻¹ ^ 2) * z⁻¹ := by
  subst z
  field_simp [hx, hy, hz0]
  ring

theorem braid_six_coefficient_identity
    (da db dz oa ob oz xT xTa xTb xTab xTba xTop : ℝ)
    (hT :
      da ^ 2 * db + oa ^ 2 * dz =
        db ^ 2 * da + ob ^ 2 * dz)
    (hTa : da * (db - dz) = db * dz)
    (hTb : db * (da - dz) = da * dz) :
    da * (db * (da * xT + oa * xTa) +
          ob * (dz * xTb + oz * xTba)) +
        oa * (dz * ((-da) * xTa + oa * xT) +
          oz * (db * xTab + ob * xTop)) =
      db * (da * (db * xT + ob * xTb) +
          oa * (dz * xTa + oz * xTab)) +
        ob * (dz * ((-db) * xTb + ob * xT) +
          oz * (da * xTba + oa * xTop)) := by
  calc
    da * (db * (da * xT + oa * xTa) +
          ob * (dz * xTb + oz * xTba)) +
        oa * (dz * ((-da) * xTa + oa * xT) +
          oz * (db * xTab + ob * xTop))
        =
      (da ^ 2 * db + oa ^ 2 * dz) * xT +
        oa * (da * (db - dz)) * xTa +
        ob * (da * dz) * xTb +
        db * oa * oz * xTab +
        da * ob * oz * xTba +
        oa * ob * oz * xTop := by
          ring
    _ =
      (db ^ 2 * da + ob ^ 2 * dz) * xT +
        oa * (db * dz) * xTa +
        ob * (db * (da - dz)) * xTb +
        db * oa * oz * xTab +
        da * ob * oz * xTba +
        oa * ob * oz * xTop := by
          rw [hT, hTa, hTb]
    _ =
      db * (da * (db * xT + ob * xTb) +
          oa * (dz * xTa + oz * xTab)) +
        ob * (dz * ((-db) * xTb + ob * xT) +
          oz * (da * xTba + oa * xTop)) := by
          ring

theorem youngAdjacentDiagCoeff_ne_zero_of_swappable {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentDiagCoeff T a ≠ 0 := by
  unfold youngAdjacentDiagCoeff
  have hx_int := adjacentAxialDistance_ne_zero_of_swappable
    T a hrow_ne hcol_ne
  have hx_real : ((adjacentAxialDistance T a : ℝ) ≠ 0) := by
    exact_mod_cast hx_int
  exact inv_ne_zero hx_real

theorem youngAdjacentDiagCoeff_sq_le_one_of_swappable {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentDiagCoeff T a ^ 2 ≤ 1 := by
  rw [sq_le_one_iff_abs_le_one]
  unfold youngAdjacentDiagCoeff
  rw [abs_inv]
  have hx_int := adjacentAxialDistance_ne_zero_of_swappable
    T a hrow_ne hcol_ne
  have hx_abs_int : (1 : Int) ≤ |adjacentAxialDistance T a| :=
    Int.one_le_abs hx_int
  have hx_abs_real : (1 : ℝ) ≤ |(adjacentAxialDistance T a : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast hx_abs_int
  exact inv_le_one_of_one_le₀ hx_abs_real

theorem adjacentAxialDistance_abs_two_le_of_swappable {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    (2 : Int) ≤ |adjacentAxialDistance T a| := by
  let x := adjacentAxialDistance T a
  have hx0 := adjacentAxialDistance_ne_zero_of_swappable T a hrow_ne hcol_ne
  have hx1 := adjacentAxialDistance_ne_one_of_swappable T a hrow_ne hcol_ne
  have hxm1 := adjacentAxialDistance_ne_neg_one_of_swappable T a hrow_ne hcol_ne
  change (2 : Int) ≤ |x|
  by_cases hx_nonneg : 0 ≤ x
  · have hxabs : |x| = x := abs_of_nonneg hx_nonneg
    omega
  · have hx_neg : x < 0 := lt_of_not_ge hx_nonneg
    have hxabs : |x| = -x := abs_of_neg hx_neg
    omega

theorem youngAdjacentDiagCoeff_sq_lt_one_of_swappable {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentDiagCoeff T a ^ 2 < 1 := by
  rw [sq_lt_one_iff_abs_lt_one]
  unfold youngAdjacentDiagCoeff
  rw [abs_inv]
  have hx_abs_int :=
    adjacentAxialDistance_abs_two_le_of_swappable T a hrow_ne hcol_ne
  have hx_abs_real :
      (2 : ℝ) ≤ |(adjacentAxialDistance T a : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast hx_abs_int
  exact inv_lt_one_of_one_lt₀ (by linarith)

theorem youngAdjacentDiagCoeff_swap {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentDiagCoeff (adjacentSwapTableau T a hrow_ne hcol_ne) a =
      - youngAdjacentDiagCoeff T a := by
  rw [youngAdjacentDiagCoeff,
    adjacentAxialDistance_swap_neg T a hrow_ne hcol_ne,
    youngAdjacentDiagCoeff]
  simp

theorem youngAdjacentOffCoeff_swap {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentOffCoeff (adjacentSwapTableau T a hrow_ne hcol_ne) a =
      youngAdjacentOffCoeff T a := by
  rw [youngAdjacentOffCoeff, youngAdjacentDiagCoeff_swap T a hrow_ne hcol_ne,
    youngAdjacentOffCoeff]
  ring_nf

theorem youngAdjacentOffCoeff_nonneg {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) :
    0 ≤ youngAdjacentOffCoeff T a := by
  exact Real.sqrt_nonneg _

theorem youngAdjacentOffCoeff_pos_of_swappable {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    0 < youngAdjacentOffCoeff T a := by
  rw [youngAdjacentOffCoeff]
  apply Real.sqrt_pos_of_pos
  have hlt := youngAdjacentDiagCoeff_sq_lt_one_of_swappable
    T a hrow_ne hcol_ne
  linarith

theorem youngAdjacentOffCoeff_ne_zero_of_swappable {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentOffCoeff T a ≠ 0 := by
  exact ne_of_gt (youngAdjacentOffCoeff_pos_of_swappable T a hrow_ne hcol_ne)

theorem youngAdjacentOffCoeff_after_disjoint_swap_eq {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hdisj : adjacentIndexDisjoint a b)
    (hrow_b :
      YoungCell.row (adjacentLoCell T b) ≠
        YoungCell.row (adjacentHiCell T b))
    (hcol_b :
      YoungCell.col (adjacentLoCell T b) ≠
        YoungCell.col (adjacentHiCell T b)) :
    youngAdjacentOffCoeff (adjacentSwapTableau T b hrow_b hcol_b) a =
      youngAdjacentOffCoeff T a := by
  rw [youngAdjacentOffCoeff, youngAdjacentOffCoeff,
    youngAdjacentDiagCoeff_after_disjoint_swap_eq T a b hdisj hrow_b hcol_b]

theorem youngAdjacentOffCoeff_sq_of_nonneg {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (h :
      0 ≤ 1 - youngAdjacentDiagCoeff T a ^ 2) :
    youngAdjacentOffCoeff T a ^ 2 =
      1 - youngAdjacentDiagCoeff T a ^ 2 := by
  rw [youngAdjacentOffCoeff, Real.sq_sqrt h]

theorem youngAdjacentCoeff_sq_sum_of_nonneg {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (h :
      0 ≤ 1 - youngAdjacentDiagCoeff T a ^ 2) :
    youngAdjacentDiagCoeff T a ^ 2 +
        youngAdjacentOffCoeff T a ^ 2 = 1 := by
  rw [youngAdjacentOffCoeff_sq_of_nonneg T a h]
  ring

theorem youngAdjacentCoeff_sq_sum_of_swappable {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentDiagCoeff T a ^ 2 +
        youngAdjacentOffCoeff T a ^ 2 = 1 := by
  apply youngAdjacentCoeff_sq_sum_of_nonneg
  have hle := youngAdjacentDiagCoeff_sq_le_one_of_swappable
    T a hrow_ne hcol_ne
  linarith

theorem not_adjacentSameRow_of_sameCol {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol : adjacentSameCol T a) :
    ¬ adjacentSameRow T a := by
  intro hrow
  exact adjacentLoCell_ne_hiCell T a
    (YoungCell.ext_row_col hrow hcol)

theorem not_adjacentSameCol_of_sameRow {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow : adjacentSameRow T a) :
    ¬ adjacentSameCol T a := by
  intro hcol
  exact adjacentLoCell_ne_hiCell T a
    (YoungCell.ext_row_col hrow hcol)

theorem not_adjacentSameRow_and_succ_sameCol {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hsucc : (b : Nat) = (a : Nat) + 1) :
    ¬ (adjacentSameRow T a ∧ adjacentSameCol T b) := by
  rintro ⟨hrow_a, hcol_b⟩
  let lo := adjacentLoCell T a
  let mid := adjacentHiCell T a
  let hi := adjacentHiCell T b
  have hmid_eq_lo_b : mid = adjacentLoCell T b := by
    simpa [mid] using adjacentHiCell_eq_loCell_of_succ T a b hsucc
  have hrow_lo_mid : YoungCell.row lo = YoungCell.row mid := by
    simpa [lo, mid, adjacentSameRow] using hrow_a
  have hcol_mid_hi : YoungCell.col mid = YoungCell.col hi := by
    have hb :
        YoungCell.col (adjacentLoCell T b) =
          YoungCell.col (adjacentHiCell T b) := by
      simpa [adjacentSameCol] using hcol_b
    simpa [mid, hi, hmid_eq_lo_b] using hb
  have hcol_lo_mid : YoungCell.col lo < YoungCell.col mid := by
    simpa [lo, mid] using adjacent_col_lt_of_sameRow T a hrow_a
  have hrow_mid_hi : YoungCell.row mid < YoungCell.row hi := by
    have hb := adjacent_row_lt_of_sameCol T b hcol_b
    simpa [mid, hi, hmid_eq_lo_b] using hb
  have hhi_box : YoungCell.col hi < youngRow lam (YoungCell.row hi) := by
    simpa [YoungCell.toNatPair, IsYoungBox] using YoungCell.isYoungBox hi
  have hcorner_box : YoungCell.col lo < youngRow lam (YoungCell.row hi) := by
    omega
  let corner : YoungCell lam :=
    youngCellOfNat lam (YoungCell.row hi) (YoungCell.col lo) hcorner_box
  have hlo_corner : T.entry lo < T.entry corner := by
    apply T.col_strict
    · simp [corner, youngCellOfNat_col]
    · simp [corner, youngCellOfNat_row]
      omega
  have hcorner_hi : T.entry corner < T.entry hi := by
    apply T.row_strict
    · simp [corner, youngCellOfNat_row]
    · simp [corner, youngCellOfNat_col]
      omega
  have hcorner_val : (T.entry corner : Nat) = (a : Nat) + 1 := by
    have hlo_corner_val : (T.entry lo : Nat) < (T.entry corner : Nat) :=
      hlo_corner
    have hcorner_hi_val : (T.entry corner : Nat) < (T.entry hi : Nat) :=
      hcorner_hi
    have hlo_val : (T.entry lo : Nat) = (a : Nat) := by
      rw [show T.entry lo = adjacentEntryLo a by
        simpa [lo] using entry_adjacentLoCell T a]
      rfl
    have hhi_val : (T.entry hi : Nat) = (a : Nat) + 2 := by
      rw [show T.entry hi = adjacentEntryHi b by
        simpa [hi] using entry_adjacentHiCell T b]
      simp [adjacentEntryHi, hsucc]
    omega
  have hcorner_entry : T.entry corner = adjacentEntryHi a := by
    apply Fin.ext
    simpa [adjacentEntryHi] using hcorner_val
  have hmid_entry : T.entry mid = adjacentEntryHi a := by
    simpa [mid] using entry_adjacentHiCell T a
  have hcorner_eq_mid : corner = mid := by
    apply T.bijective.1
    rw [hcorner_entry, hmid_entry]
  have hrow_corner_mid :
      YoungCell.row corner = YoungCell.row mid := by
    exact congrArg YoungCell.row hcorner_eq_mid
  have hrow_corner_hi : YoungCell.row corner = YoungCell.row hi := by
    simp [corner, youngCellOfNat_row]
  omega

theorem not_adjacentSameCol_and_succ_sameRow {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hsucc : (b : Nat) = (a : Nat) + 1) :
    ¬ (adjacentSameCol T a ∧ adjacentSameRow T b) := by
  rintro ⟨hcol_a, hrow_b⟩
  let lo := adjacentLoCell T a
  let mid := adjacentHiCell T a
  let hi := adjacentHiCell T b
  have hmid_eq_lo_b : mid = adjacentLoCell T b := by
    simpa [mid] using adjacentHiCell_eq_loCell_of_succ T a b hsucc
  have hcol_lo_mid : YoungCell.col lo = YoungCell.col mid := by
    simpa [lo, mid, adjacentSameCol] using hcol_a
  have hrow_mid_hi : YoungCell.row mid = YoungCell.row hi := by
    have hb :
        YoungCell.row (adjacentLoCell T b) =
          YoungCell.row (adjacentHiCell T b) := by
      simpa [adjacentSameRow] using hrow_b
    simpa [mid, hi, hmid_eq_lo_b] using hb
  have hrow_lo_mid : YoungCell.row lo < YoungCell.row mid := by
    simpa [lo, mid] using adjacent_row_lt_of_sameCol T a hcol_a
  have hcol_mid_hi : YoungCell.col mid < YoungCell.col hi := by
    have hb := adjacent_col_lt_of_sameRow T b hrow_b
    simpa [mid, hi, hmid_eq_lo_b] using hb
  have hhi_box : YoungCell.col hi < youngRow lam (YoungCell.row hi) := by
    simpa [YoungCell.toNatPair, IsYoungBox] using YoungCell.isYoungBox hi
  have hrow_le :
      youngRow lam (YoungCell.row hi) <= youngRow lam (YoungCell.row lo) :=
    youngRow_le_of_le lam (by omega)
  have hcorner_box : YoungCell.col hi < youngRow lam (YoungCell.row lo) := by
    omega
  let corner : YoungCell lam :=
    youngCellOfNat lam (YoungCell.row lo) (YoungCell.col hi) hcorner_box
  have hlo_corner : T.entry lo < T.entry corner := by
    apply T.row_strict
    · simp [corner, youngCellOfNat_row]
    · simp [corner, youngCellOfNat_col]
      omega
  have hcorner_hi : T.entry corner < T.entry hi := by
    apply T.col_strict
    · simp [corner, youngCellOfNat_col]
    · simp [corner, youngCellOfNat_row]
      omega
  have hcorner_val : (T.entry corner : Nat) = (a : Nat) + 1 := by
    have hlo_corner_val : (T.entry lo : Nat) < (T.entry corner : Nat) :=
      hlo_corner
    have hcorner_hi_val : (T.entry corner : Nat) < (T.entry hi : Nat) :=
      hcorner_hi
    have hlo_val : (T.entry lo : Nat) = (a : Nat) := by
      rw [show T.entry lo = adjacentEntryLo a by
        simpa [lo] using entry_adjacentLoCell T a]
      rfl
    have hhi_val : (T.entry hi : Nat) = (a : Nat) + 2 := by
      rw [show T.entry hi = adjacentEntryHi b by
        simpa [hi] using entry_adjacentHiCell T b]
      simp [adjacentEntryHi, hsucc]
    omega
  have hcorner_entry : T.entry corner = adjacentEntryHi a := by
    apply Fin.ext
    simpa [adjacentEntryHi] using hcorner_val
  have hmid_entry : T.entry mid = adjacentEntryHi a := by
    simpa [mid] using entry_adjacentHiCell T a
  have hcorner_eq_mid : corner = mid := by
    apply T.bijective.1
    rw [hcorner_entry, hmid_entry]
  have hrow_corner_mid :
      YoungCell.row corner = YoungCell.row mid := by
    exact congrArg YoungCell.row hcorner_eq_mid
  have hrow_corner_lo : YoungCell.row corner = YoungCell.row lo := by
    simp [corner, youngCellOfNat_row]
  omega

theorem not_adjacentSameRow_after_right_swap_of_left_sameRow_of_succ
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hsucc : (b : Nat) = (a : Nat) + 1)
    (hrow_a : adjacentSameRow T a)
    (hrow_b : ¬ adjacentSameRow T b)
    (hcol_b : ¬ adjacentSameCol T b) :
    ¬ adjacentSameRow (adjacentSwapTableau T b hrow_b hcol_b) a := by
  intro hrow_after
  let Tb := adjacentSwapTableau T b hrow_b hcol_b
  have hhi_lo : adjacentHiCell T a = adjacentLoCell T b := by
    simpa using adjacentHiCell_eq_loCell_of_succ T a b hsucc
  have hlo_a_ne_lo_b : adjacentEntryLo a ≠ adjacentEntryLo b := by
    intro h
    have hv := congrArg Fin.val h
    simp [adjacentEntryLo, hsucc] at hv
  have hlo_a_ne_hi_b : adjacentEntryLo a ≠ adjacentEntryHi b := by
    intro h
    have hv := congrArg Fin.val h
    simp [adjacentEntryLo, adjacentEntryHi, hsucc] at hv
    omega
  have hlo_after :
      adjacentLoCell Tb a = adjacentLoCell T a := by
    unfold adjacentLoCell
    rw [adjacentSwapTableau_cell_of_ne_lo_hi T b hrow_b hcol_b
      hlo_a_ne_lo_b hlo_a_ne_hi_b]
  have hhi_after :
      adjacentHiCell Tb a = adjacentHiCell T b := by
    unfold adjacentHiCell
    rw [show adjacentEntryHi a = adjacentEntryLo b by
      exact adjacentEntryHi_eq_lo_of_succ a b hsucc]
    exact adjacentSwapTableau_cell_lo T b hrow_b hcol_b
  have hrow_lo_a_hi_b :
      YoungCell.row (adjacentLoCell T a) =
        YoungCell.row (adjacentHiCell T b) := by
    simpa [adjacentSameRow, hlo_after, hhi_after, Tb] using hrow_after
  have hrow_b_raw : adjacentSameRow T b := by
    calc
      YoungCell.row (adjacentLoCell T b)
          = YoungCell.row (adjacentHiCell T a) := by rw [← hhi_lo]
      _ = YoungCell.row (adjacentLoCell T a) := by
            simpa [adjacentSameRow] using hrow_a.symm
      _ = YoungCell.row (adjacentHiCell T b) := hrow_lo_a_hi_b
  exact hrow_b hrow_b_raw

theorem not_adjacentSameCol_after_right_swap_of_left_sameCol_of_succ
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hsucc : (b : Nat) = (a : Nat) + 1)
    (hcol_a : adjacentSameCol T a)
    (hrow_b : ¬ adjacentSameRow T b)
    (hcol_b : ¬ adjacentSameCol T b) :
    ¬ adjacentSameCol (adjacentSwapTableau T b hrow_b hcol_b) a := by
  intro hcol_after
  let Tb := adjacentSwapTableau T b hrow_b hcol_b
  have hhi_lo : adjacentHiCell T a = adjacentLoCell T b := by
    simpa using adjacentHiCell_eq_loCell_of_succ T a b hsucc
  have hlo_a_ne_lo_b : adjacentEntryLo a ≠ adjacentEntryLo b := by
    intro h
    have hv := congrArg Fin.val h
    simp [adjacentEntryLo, hsucc] at hv
  have hlo_a_ne_hi_b : adjacentEntryLo a ≠ adjacentEntryHi b := by
    intro h
    have hv := congrArg Fin.val h
    simp [adjacentEntryLo, adjacentEntryHi, hsucc] at hv
    omega
  have hlo_after :
      adjacentLoCell Tb a = adjacentLoCell T a := by
    unfold adjacentLoCell
    rw [adjacentSwapTableau_cell_of_ne_lo_hi T b hrow_b hcol_b
      hlo_a_ne_lo_b hlo_a_ne_hi_b]
  have hhi_after :
      adjacentHiCell Tb a = adjacentHiCell T b := by
    unfold adjacentHiCell
    rw [show adjacentEntryHi a = adjacentEntryLo b by
      exact adjacentEntryHi_eq_lo_of_succ a b hsucc]
    exact adjacentSwapTableau_cell_lo T b hrow_b hcol_b
  have hcol_lo_a_hi_b :
      YoungCell.col (adjacentLoCell T a) =
        YoungCell.col (adjacentHiCell T b) := by
    simpa [adjacentSameCol, hlo_after, hhi_after, Tb] using hcol_after
  have hcol_b_raw : adjacentSameCol T b := by
    calc
      YoungCell.col (adjacentLoCell T b)
          = YoungCell.col (adjacentHiCell T a) := by rw [← hhi_lo]
      _ = YoungCell.col (adjacentLoCell T a) := by
            simpa [adjacentSameCol] using hcol_a.symm
      _ = YoungCell.col (adjacentHiCell T b) := hcol_lo_a_hi_b
  exact hcol_b hcol_b_raw

theorem not_adjacentSameRow_after_left_swap_of_right_sameRow_of_succ
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hsucc : (b : Nat) = (a : Nat) + 1)
    (hrow_b : adjacentSameRow T b)
    (hrow_a : ¬ adjacentSameRow T a)
    (hcol_a : ¬ adjacentSameCol T a) :
    ¬ adjacentSameRow (adjacentSwapTableau T a hrow_a hcol_a) b := by
  intro hrow_after
  let Ta := adjacentSwapTableau T a hrow_a hcol_a
  have hhi_lo : adjacentHiCell T a = adjacentLoCell T b := by
    simpa using adjacentHiCell_eq_loCell_of_succ T a b hsucc
  have hhi_b_ne_lo_a : adjacentEntryHi b ≠ adjacentEntryLo a := by
    intro h
    have hv := congrArg Fin.val h
    simp [adjacentEntryHi, adjacentEntryLo, hsucc] at hv
    omega
  have hhi_b_ne_hi_a : adjacentEntryHi b ≠ adjacentEntryHi a := by
    intro h
    have hv := congrArg Fin.val h
    simp [adjacentEntryHi, hsucc] at hv
  have hlo_after :
      adjacentLoCell Ta b = adjacentLoCell T a := by
    unfold adjacentLoCell
    rw [show adjacentEntryLo b = adjacentEntryHi a by
      exact (adjacentEntryHi_eq_lo_of_succ a b hsucc).symm]
    exact adjacentSwapTableau_cell_hi T a hrow_a hcol_a
  have hhi_after :
      adjacentHiCell Ta b = adjacentHiCell T b := by
    unfold adjacentHiCell
    rw [adjacentSwapTableau_cell_of_ne_lo_hi T a hrow_a hcol_a
      hhi_b_ne_lo_a hhi_b_ne_hi_a]
  have hrow_lo_a_hi_b :
      YoungCell.row (adjacentLoCell T a) =
        YoungCell.row (adjacentHiCell T b) := by
    simpa [adjacentSameRow, hlo_after, hhi_after, Ta] using hrow_after
  have hrow_a_raw : adjacentSameRow T a := by
    calc
      YoungCell.row (adjacentLoCell T a)
          = YoungCell.row (adjacentHiCell T b) := hrow_lo_a_hi_b
      _ = YoungCell.row (adjacentLoCell T b) := by
            simpa [adjacentSameRow] using hrow_b.symm
      _ = YoungCell.row (adjacentHiCell T a) := by rw [← hhi_lo]
  exact hrow_a hrow_a_raw

theorem not_adjacentSameCol_after_left_swap_of_right_sameCol_of_succ
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hsucc : (b : Nat) = (a : Nat) + 1)
    (hcol_b : adjacentSameCol T b)
    (hrow_a : ¬ adjacentSameRow T a)
    (hcol_a : ¬ adjacentSameCol T a) :
    ¬ adjacentSameCol (adjacentSwapTableau T a hrow_a hcol_a) b := by
  intro hcol_after
  let Ta := adjacentSwapTableau T a hrow_a hcol_a
  have hhi_lo : adjacentHiCell T a = adjacentLoCell T b := by
    simpa using adjacentHiCell_eq_loCell_of_succ T a b hsucc
  have hhi_b_ne_lo_a : adjacentEntryHi b ≠ adjacentEntryLo a := by
    intro h
    have hv := congrArg Fin.val h
    simp [adjacentEntryHi, adjacentEntryLo, hsucc] at hv
    omega
  have hhi_b_ne_hi_a : adjacentEntryHi b ≠ adjacentEntryHi a := by
    intro h
    have hv := congrArg Fin.val h
    simp [adjacentEntryHi, hsucc] at hv
  have hlo_after :
      adjacentLoCell Ta b = adjacentLoCell T a := by
    unfold adjacentLoCell
    rw [show adjacentEntryLo b = adjacentEntryHi a by
      exact (adjacentEntryHi_eq_lo_of_succ a b hsucc).symm]
    exact adjacentSwapTableau_cell_hi T a hrow_a hcol_a
  have hhi_after :
      adjacentHiCell Ta b = adjacentHiCell T b := by
    unfold adjacentHiCell
    rw [adjacentSwapTableau_cell_of_ne_lo_hi T a hrow_a hcol_a
      hhi_b_ne_lo_a hhi_b_ne_hi_a]
  have hcol_lo_a_hi_b :
      YoungCell.col (adjacentLoCell T a) =
        YoungCell.col (adjacentHiCell T b) := by
    simpa [adjacentSameCol, hlo_after, hhi_after, Ta] using hcol_after
  have hcol_a_raw : adjacentSameCol T a := by
    calc
      YoungCell.col (adjacentLoCell T a)
          = YoungCell.col (adjacentHiCell T b) := hcol_lo_a_hi_b
      _ = YoungCell.col (adjacentLoCell T b) := by
            simpa [adjacentSameCol] using hcol_b.symm
      _ = YoungCell.col (adjacentHiCell T a) := by rw [← hhi_lo]
  exact hcol_a hcol_a_raw

theorem adjacentSwapTableau_ne_self {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    adjacentSwapTableau T a hrow_ne hcol_ne ≠ T := by
  intro h
  have hentry :=
    congrArg (fun U : StandardYoungTableau lam =>
      U.entry (adjacentLoCell T a)) h
  change adjacentSwapEntry T a (adjacentLoCell T a) =
    T.entry (adjacentLoCell T a) at hentry
  rw [adjacentSwapEntry_loCell, entry_adjacentLoCell] at hentry
  exact adjacentEntryLo_ne_hi a hentry.symm

theorem adjacentSameRow_swap_iff {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    adjacentSameRow (adjacentSwapTableau T a hrow_ne hcol_ne) a ↔
      adjacentSameRow T a := by
  unfold adjacentSameRow adjacentLoCell adjacentHiCell
  rw [adjacentSwapTableau_cell_lo, adjacentSwapTableau_cell_hi]
  exact eq_comm

theorem adjacentSameCol_swap_iff {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    adjacentSameCol (adjacentSwapTableau T a hrow_ne hcol_ne) a ↔
      adjacentSameCol T a := by
  unfold adjacentSameCol adjacentLoCell adjacentHiCell
  rw [adjacentSwapTableau_cell_lo, adjacentSwapTableau_cell_hi]
  exact eq_comm

theorem not_adjacentSameRow_swap {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    ¬ adjacentSameRow (adjacentSwapTableau T a hrow_ne hcol_ne) a := by
  intro h
  exact hrow_ne ((adjacentSameRow_swap_iff T a hrow_ne hcol_ne).1 h)

theorem not_adjacentSameCol_swap {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    ¬ adjacentSameCol (adjacentSwapTableau T a hrow_ne hcol_ne) a := by
  intro h
  exact hcol_ne ((adjacentSameCol_swap_iff T a hrow_ne hcol_ne).1 h)

theorem adjacentSwapTableau_involutive {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a)
    (hrow_ne' :
      ¬ adjacentSameRow (adjacentSwapTableau T a hrow_ne hcol_ne) a)
    (hcol_ne' :
      ¬ adjacentSameCol (adjacentSwapTableau T a hrow_ne hcol_ne) a) :
    adjacentSwapTableau
        (adjacentSwapTableau T a hrow_ne hcol_ne) a hrow_ne' hcol_ne' =
      T := by
  apply standardYoungTableau_ext_entry
  intro u
  simp [adjacentSwapTableau, adjacentSwapEntry, adjacentSwapValue_involutive]

theorem ne_adjacentSwapTableau_of_sameRow {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T S : StandardYoungTableau lam) (a : Fin n)
    (hrowT : adjacentSameRow T a)
    (hrowS_ne : ¬ adjacentSameRow S a)
    (hcolS_ne : ¬ adjacentSameCol S a) :
    T ≠ adjacentSwapTableau S a hrowS_ne hcolS_ne := by
  intro h
  have hswap_row :
      adjacentSameRow (adjacentSwapTableau S a hrowS_ne hcolS_ne) a := by
    simpa [h] using hrowT
  exact hrowS_ne
    ((adjacentSameRow_swap_iff S a hrowS_ne hcolS_ne).1 hswap_row)

theorem ne_adjacentSwapTableau_of_sameCol {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T S : StandardYoungTableau lam) (a : Fin n)
    (hcolT : adjacentSameCol T a)
    (hrowS_ne : ¬ adjacentSameRow S a)
    (hcolS_ne : ¬ adjacentSameCol S a) :
    T ≠ adjacentSwapTableau S a hrowS_ne hcolS_ne := by
  intro h
  have hswap_col :
      adjacentSameCol (adjacentSwapTableau S a hrowS_ne hcolS_ne) a := by
    simpa [h] using hcolT
  exact hcolS_ne
    ((adjacentSameCol_swap_iff S a hrowS_ne hcolS_ne).1 hswap_col)

theorem ne_adjacentSwapTableau_of_ne_swapped {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T S : StandardYoungTableau lam) (a : Fin n)
    (hrowT_ne : ¬ adjacentSameRow T a)
    (hcolT_ne : ¬ adjacentSameCol T a)
    (hrowS_ne : ¬ adjacentSameRow S a)
    (hcolS_ne : ¬ adjacentSameCol S a)
    (hS_ne_swapT :
      S ≠ adjacentSwapTableau T a hrowT_ne hcolT_ne) :
    T ≠ adjacentSwapTableau S a hrowS_ne hcolS_ne := by
  intro h
  subst T
  have hinv :
      adjacentSwapTableau
          (adjacentSwapTableau S a hrowS_ne hcolS_ne) a
          hrowT_ne hcolT_ne = S :=
    adjacentSwapTableau_involutive S a hrowS_ne hcolS_ne
      hrowT_ne hcolT_ne
  exact hS_ne_swapT hinv.symm

/-- Matrix coefficient of the Young adjacent-transposition formula in the
standard tableau basis.  This is only the concrete coefficient model, not yet a
claim that it realizes a symmetric-group representation. -/
noncomputable def youngAdjacentMatrixCoeff {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (a : Fin n) (S T : StandardYoungTableau lam) : ℝ :=
  if hrow : adjacentSameRow T a then
    if S = T then 1 else 0
  else if hcol : adjacentSameCol T a then
    if S = T then -1 else 0
  else
    if S = T then youngAdjacentDiagCoeff T a
    else if S = adjacentSwapTableau T a hrow hcol then
      youngAdjacentOffCoeff T a
    else 0

theorem youngAdjacentMatrixCoeff_sameRow_self {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow : adjacentSameRow T a) :
    youngAdjacentMatrixCoeff a T T = 1 := by
  simp [youngAdjacentMatrixCoeff, hrow]

theorem youngAdjacentMatrixCoeff_sameRow_ne {n : Nat}
    {lam : YoungDiagram (n + 1)}
    {S T : StandardYoungTableau lam} (a : Fin n)
    (hrow : adjacentSameRow T a) (hST : S ≠ T) :
    youngAdjacentMatrixCoeff a S T = 0 := by
  simp [youngAdjacentMatrixCoeff, hrow, hST]

theorem youngAdjacentMatrixCoeff_sameCol_self {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol : adjacentSameCol T a) :
    youngAdjacentMatrixCoeff a T T = -1 := by
  have hrow_ne := not_adjacentSameRow_of_sameCol T a hcol
  simp [youngAdjacentMatrixCoeff, hrow_ne, hcol]

theorem youngAdjacentMatrixCoeff_sameCol_ne {n : Nat}
    {lam : YoungDiagram (n + 1)}
    {S T : StandardYoungTableau lam} (a : Fin n)
    (hcol : adjacentSameCol T a) (hST : S ≠ T) :
    youngAdjacentMatrixCoeff a S T = 0 := by
  have hrow_ne := not_adjacentSameRow_of_sameCol T a hcol
  simp [youngAdjacentMatrixCoeff, hrow_ne, hcol, hST]

theorem youngAdjacentMatrixCoeff_swappable_self {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentMatrixCoeff a T T = youngAdjacentDiagCoeff T a := by
  simp [youngAdjacentMatrixCoeff, hrow_ne, hcol_ne]

theorem youngAdjacentMatrixCoeff_swappable_swap {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentMatrixCoeff a
        (adjacentSwapTableau T a hrow_ne hcol_ne) T =
      youngAdjacentOffCoeff T a := by
  have hswap_ne := adjacentSwapTableau_ne_self T a hrow_ne hcol_ne
  simp [youngAdjacentMatrixCoeff, hrow_ne, hcol_ne, hswap_ne]

theorem youngAdjacentMatrixCoeff_swappable_swap_symm {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentMatrixCoeff a T
        (adjacentSwapTableau T a hrow_ne hcol_ne) =
      youngAdjacentOffCoeff T a := by
  let T' := adjacentSwapTableau T a hrow_ne hcol_ne
  have hrow_ne' : ¬ adjacentSameRow T' a := by
    simpa [T'] using not_adjacentSameRow_swap T a hrow_ne hcol_ne
  have hcol_ne' : ¬ adjacentSameCol T' a := by
    simpa [T'] using not_adjacentSameCol_swap T a hrow_ne hcol_ne
  have h :=
    youngAdjacentMatrixCoeff_swappable_swap T' a hrow_ne' hcol_ne'
  have hinv :
      adjacentSwapTableau T' a hrow_ne' hcol_ne' = T := by
    simpa [T'] using
      adjacentSwapTableau_involutive T a hrow_ne hcol_ne hrow_ne' hcol_ne'
  have hoff :
      youngAdjacentOffCoeff T' a = youngAdjacentOffCoeff T a := by
    simpa [T'] using youngAdjacentOffCoeff_swap T a hrow_ne hcol_ne
  simpa [T', hinv, hoff] using h

theorem youngAdjacentMatrixCoeff_swappable_pair_symmetric {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentMatrixCoeff a
        (adjacentSwapTableau T a hrow_ne hcol_ne) T =
      youngAdjacentMatrixCoeff a T
        (adjacentSwapTableau T a hrow_ne hcol_ne) := by
  rw [youngAdjacentMatrixCoeff_swappable_swap,
    youngAdjacentMatrixCoeff_swappable_swap_symm]

theorem youngAdjacentMatrixCoeff_swappable_other {n : Nat}
    {lam : YoungDiagram (n + 1)}
    {S T : StandardYoungTableau lam} (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a)
    (hST : S ≠ T)
    (hSswap : S ≠ adjacentSwapTableau T a hrow_ne hcol_ne) :
    youngAdjacentMatrixCoeff a S T = 0 := by
  simp [youngAdjacentMatrixCoeff, hrow_ne, hcol_ne, hST, hSswap]

theorem youngAdjacentMatrixCoeff_target_sameRow_ne {n : Nat}
    {lam : YoungDiagram (n + 1)}
    {S T : StandardYoungTableau lam} (a : Fin n)
    (hrowT : adjacentSameRow T a) (hST : S ≠ T) :
    youngAdjacentMatrixCoeff a T S = 0 := by
  by_cases hrowS : adjacentSameRow S a
  · exact youngAdjacentMatrixCoeff_sameRow_ne (S := T) (T := S)
      a hrowS hST.symm
  · by_cases hcolS : adjacentSameCol S a
    · exact youngAdjacentMatrixCoeff_sameCol_ne (S := T) (T := S)
        a hcolS hST.symm
    · exact youngAdjacentMatrixCoeff_swappable_other (S := T) (T := S)
        a hrowS hcolS hST.symm
        (ne_adjacentSwapTableau_of_sameRow T S a hrowT hrowS hcolS)

theorem youngAdjacentMatrixCoeff_target_sameCol_ne {n : Nat}
    {lam : YoungDiagram (n + 1)}
    {S T : StandardYoungTableau lam} (a : Fin n)
    (hcolT : adjacentSameCol T a) (hST : S ≠ T) :
    youngAdjacentMatrixCoeff a T S = 0 := by
  by_cases hrowS : adjacentSameRow S a
  · exact youngAdjacentMatrixCoeff_sameRow_ne (S := T) (T := S)
      a hrowS hST.symm
  · by_cases hcolS : adjacentSameCol S a
    · exact youngAdjacentMatrixCoeff_sameCol_ne (S := T) (T := S)
        a hcolS hST.symm
    · exact youngAdjacentMatrixCoeff_swappable_other (S := T) (T := S)
        a hrowS hcolS hST.symm
        (ne_adjacentSwapTableau_of_sameCol T S a hcolT hrowS hcolS)

theorem youngAdjacentMatrixCoeff_symmetric_of_source_sameRow {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (S T : StandardYoungTableau lam) (a : Fin n)
    (hrowT : adjacentSameRow T a) :
    youngAdjacentMatrixCoeff a S T =
      youngAdjacentMatrixCoeff a T S := by
  by_cases hST : S = T
  · subst S
    rfl
  · rw [youngAdjacentMatrixCoeff_sameRow_ne a hrowT hST,
      youngAdjacentMatrixCoeff_target_sameRow_ne a hrowT hST]

theorem youngAdjacentMatrixCoeff_symmetric_of_source_sameCol {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (S T : StandardYoungTableau lam) (a : Fin n)
    (hcolT : adjacentSameCol T a) :
    youngAdjacentMatrixCoeff a S T =
      youngAdjacentMatrixCoeff a T S := by
  by_cases hST : S = T
  · subst S
    rfl
  · rw [youngAdjacentMatrixCoeff_sameCol_ne a hcolT hST,
      youngAdjacentMatrixCoeff_target_sameCol_ne a hcolT hST]

theorem youngAdjacentMatrixCoeff_symmetric_of_source_swappable {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (S T : StandardYoungTableau lam) (a : Fin n)
    (hrowT_ne : ¬ adjacentSameRow T a)
    (hcolT_ne : ¬ adjacentSameCol T a) :
    youngAdjacentMatrixCoeff a S T =
      youngAdjacentMatrixCoeff a T S := by
  by_cases hST : S = T
  · subst S
    rfl
  · by_cases hSswap : S = adjacentSwapTableau T a hrowT_ne hcolT_ne
    · subst S
      exact youngAdjacentMatrixCoeff_swappable_pair_symmetric T a
        hrowT_ne hcolT_ne
    · rw [youngAdjacentMatrixCoeff_swappable_other a hrowT_ne hcolT_ne
        hST hSswap]
      by_cases hrowS : adjacentSameRow S a
      · rw [youngAdjacentMatrixCoeff_sameRow_ne (S := T) (T := S)
          a hrowS (fun h => hST h.symm)]
      · by_cases hcolS : adjacentSameCol S a
        · rw [youngAdjacentMatrixCoeff_sameCol_ne (S := T) (T := S)
            a hcolS (fun h => hST h.symm)]
        · rw [youngAdjacentMatrixCoeff_swappable_other (S := T) (T := S)
            a hrowS hcolS (fun h => hST h.symm)
            (ne_adjacentSwapTableau_of_ne_swapped T S a
              hrowT_ne hcolT_ne hrowS hcolS hSswap)]

theorem youngAdjacentMatrixCoeff_symmetric {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (a : Fin n) (S T : StandardYoungTableau lam) :
    youngAdjacentMatrixCoeff a S T =
      youngAdjacentMatrixCoeff a T S := by
  by_cases hrowT : adjacentSameRow T a
  · exact youngAdjacentMatrixCoeff_symmetric_of_source_sameRow S T a hrowT
  · by_cases hcolT : adjacentSameCol T a
    · exact youngAdjacentMatrixCoeff_symmetric_of_source_sameCol S T a hcolT
    · exact youngAdjacentMatrixCoeff_symmetric_of_source_swappable
        S T a hrowT hcolT

/-- The adjacent-transposition matrix on the tableau coordinate space.  This is
the explicit Young-orthogonal matrix model on a single shape. -/
noncomputable def youngAdjacentOperator {n : Nat}
    {lam : YoungDiagram (n + 1)} (a : Fin n) :
    TableauSpace lam -> TableauSpace lam :=
  fun f S =>
    ∑ T : StandardYoungTableau lam, youngAdjacentMatrixCoeff a S T * f T

theorem youngAdjacentOperator_basis_value {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (a : Fin n) (S T : StandardYoungTableau lam) :
    youngAdjacentOperator a (tableauBasisVec T) S =
      youngAdjacentMatrixCoeff a S T := by
  classical
  rw [youngAdjacentOperator]
  rw [Fintype.sum_eq_single T]
  · simp [tableauBasisVec]
  · intro U hU
    simp [tableauBasisVec, hU]

theorem youngAdjacentOperator_basis_sameRow {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow : adjacentSameRow T a) :
    youngAdjacentOperator a (tableauBasisVec T) = tableauBasisVec T := by
  funext S
  by_cases hST : S = T
  · subst S
    rw [youngAdjacentOperator_basis_value,
      youngAdjacentMatrixCoeff_sameRow_self]
    · simp
    · exact hrow
  · rw [youngAdjacentOperator_basis_value,
      youngAdjacentMatrixCoeff_sameRow_ne a hrow hST,
      tableauBasisVec_ne hST]

theorem youngAdjacentOperator_basis_sameCol {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol : adjacentSameCol T a) :
    youngAdjacentOperator a (tableauBasisVec T) =
      fun S => - tableauBasisVec T S := by
  funext S
  by_cases hST : S = T
  · subst S
    rw [youngAdjacentOperator_basis_value,
      youngAdjacentMatrixCoeff_sameCol_self]
    · simp
    · exact hcol
  · rw [youngAdjacentOperator_basis_value,
      youngAdjacentMatrixCoeff_sameCol_ne a hcol hST,
      tableauBasisVec_ne hST]
    simp

theorem youngAdjacentOperator_basis_swappable_self_value {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentOperator a (tableauBasisVec T) T =
      youngAdjacentDiagCoeff T a := by
  rw [youngAdjacentOperator_basis_value,
    youngAdjacentMatrixCoeff_swappable_self T a hrow_ne hcol_ne]

theorem youngAdjacentOperator_basis_swappable_swap_value {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentOperator a (tableauBasisVec T)
        (adjacentSwapTableau T a hrow_ne hcol_ne) =
      youngAdjacentOffCoeff T a := by
  rw [youngAdjacentOperator_basis_value,
    youngAdjacentMatrixCoeff_swappable_swap T a hrow_ne hcol_ne]

theorem youngAdjacentOperator_basis_swappable_swap_symm_value {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentOperator a
        (tableauBasisVec (adjacentSwapTableau T a hrow_ne hcol_ne)) T =
      youngAdjacentOffCoeff T a := by
  rw [youngAdjacentOperator_basis_value,
    youngAdjacentMatrixCoeff_swappable_swap_symm T a hrow_ne hcol_ne]

theorem youngAdjacentOperator_selfAdjoint_basis_swappable_pair {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    tableauInner
        (youngAdjacentOperator a (tableauBasisVec T))
        (tableauBasisVec (adjacentSwapTableau T a hrow_ne hcol_ne)) =
      tableauInner
        (tableauBasisVec T)
        (youngAdjacentOperator a
          (tableauBasisVec (adjacentSwapTableau T a hrow_ne hcol_ne))) := by
  rw [tableauInner_right_basis, tableauInner_left_basis,
    youngAdjacentOperator_basis_swappable_swap_value,
    youngAdjacentOperator_basis_swappable_swap_symm_value]

theorem youngAdjacentOperator_selfAdjoint_basis {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (a : Fin n) (S T : StandardYoungTableau lam) :
    tableauInner
        (youngAdjacentOperator a (tableauBasisVec T))
        (tableauBasisVec S) =
      tableauInner
        (tableauBasisVec T)
        (youngAdjacentOperator a (tableauBasisVec S)) := by
  rw [tableauInner_right_basis, tableauInner_left_basis,
    youngAdjacentOperator_basis_value, youngAdjacentOperator_basis_value,
    youngAdjacentMatrixCoeff_symmetric]

theorem youngAdjacentOperator_basis_swappable_other_value {n : Nat}
    {lam : YoungDiagram (n + 1)}
    {S T : StandardYoungTableau lam} (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a)
    (hST : S ≠ T)
    (hSswap : S ≠ adjacentSwapTableau T a hrow_ne hcol_ne) :
    youngAdjacentOperator a (tableauBasisVec T) S = 0 := by
  rw [youngAdjacentOperator_basis_value,
    youngAdjacentMatrixCoeff_swappable_other a hrow_ne hcol_ne hST hSswap]

theorem youngAdjacentOperator_neg {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (a : Fin n) (f : TableauSpace lam) :
    youngAdjacentOperator a (fun S => - f S) =
      fun S => - youngAdjacentOperator a f S := by
  funext S
  unfold youngAdjacentOperator
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro T _
  ring

theorem youngAdjacentOperator_add {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (a : Fin n) (f g : TableauSpace lam) :
    youngAdjacentOperator a (fun S => f S + g S) =
      fun S => youngAdjacentOperator a f S +
        youngAdjacentOperator a g S := by
  funext S
  unfold youngAdjacentOperator
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T _
  ring

theorem youngAdjacentOperator_smul {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (a : Fin n) (c : ℝ) (f : TableauSpace lam) :
    youngAdjacentOperator a (fun S => c * f S) =
      fun S => c * youngAdjacentOperator a f S := by
  funext S
  unfold youngAdjacentOperator
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  ring

theorem youngAdjacentOperator_sum {n : Nat} {ι : Type}
    {lam : YoungDiagram (n + 1)} [Fintype ι]
    (a : Fin n) (f : ι -> TableauSpace lam) :
    youngAdjacentOperator a (fun S => ∑ i : ι, f i S) =
      fun S => ∑ i : ι, youngAdjacentOperator a (f i) S := by
  classical
  funext S
  unfold youngAdjacentOperator
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

theorem youngAdjacentOperator_sq_basis_sameRow {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow : adjacentSameRow T a) :
    youngAdjacentOperator a
        (youngAdjacentOperator a (tableauBasisVec T)) =
      tableauBasisVec T := by
  rw [youngAdjacentOperator_basis_sameRow T a hrow,
    youngAdjacentOperator_basis_sameRow T a hrow]

theorem youngAdjacentOperator_sq_basis_sameCol {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol : adjacentSameCol T a) :
    youngAdjacentOperator a
        (youngAdjacentOperator a (tableauBasisVec T)) =
      tableauBasisVec T := by
  rw [youngAdjacentOperator_basis_sameCol T a hcol,
    youngAdjacentOperator_neg,
    youngAdjacentOperator_basis_sameCol T a hcol]
  funext S
  simp

theorem youngAdjacentOperator_basis_swappable_eq {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentOperator a (tableauBasisVec T) =
      fun S =>
        youngAdjacentDiagCoeff T a * tableauBasisVec T S +
          youngAdjacentOffCoeff T a *
            tableauBasisVec (adjacentSwapTableau T a hrow_ne hcol_ne) S := by
  funext S
  let T' := adjacentSwapTableau T a hrow_ne hcol_ne
  have hT'_ne_T : T' ≠ T := by
    simpa [T'] using adjacentSwapTableau_ne_self T a hrow_ne hcol_ne
  by_cases hST : S = T
  · subst S
    rw [youngAdjacentOperator_basis_swappable_self_value T a hrow_ne hcol_ne]
    rw [tableauBasisVec_self, tableauBasisVec_ne hT'_ne_T.symm]
    ring
  · by_cases hST' : S = T'
    · subst S
      rw [youngAdjacentOperator_basis_swappable_swap_value T a hrow_ne hcol_ne]
      rw [tableauBasisVec_ne hT'_ne_T, tableauBasisVec_self]
      ring
    · rw [youngAdjacentOperator_basis_swappable_other_value a hrow_ne hcol_ne
        hST (by simpa [T'] using hST')]
      rw [tableauBasisVec_ne hST, tableauBasisVec_ne hST']
      ring

theorem youngAdjacentOperator_basis_swappable_swap_eq {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentOperator a
        (tableauBasisVec (adjacentSwapTableau T a hrow_ne hcol_ne)) =
      fun S =>
        youngAdjacentOffCoeff T a * tableauBasisVec T S -
          youngAdjacentDiagCoeff T a *
            tableauBasisVec (adjacentSwapTableau T a hrow_ne hcol_ne) S := by
  let T' := adjacentSwapTableau T a hrow_ne hcol_ne
  have hrow_ne' : ¬ adjacentSameRow T' a := by
    simpa [T'] using not_adjacentSameRow_swap T a hrow_ne hcol_ne
  have hcol_ne' : ¬ adjacentSameCol T' a := by
    simpa [T'] using not_adjacentSameCol_swap T a hrow_ne hcol_ne
  have hswap :
      adjacentSwapTableau T' a hrow_ne' hcol_ne' = T := by
    simpa [T'] using
      adjacentSwapTableau_involutive T a hrow_ne hcol_ne hrow_ne' hcol_ne'
  have hdiag :
      youngAdjacentDiagCoeff T' a = - youngAdjacentDiagCoeff T a := by
    simpa [T'] using youngAdjacentDiagCoeff_swap T a hrow_ne hcol_ne
  have hoff :
      youngAdjacentOffCoeff T' a = youngAdjacentOffCoeff T a := by
    simpa [T'] using youngAdjacentOffCoeff_swap T a hrow_ne hcol_ne
  rw [show adjacentSwapTableau T a hrow_ne hcol_ne = T' by rfl]
  rw [youngAdjacentOperator_basis_swappable_eq T' a hrow_ne' hcol_ne']
  funext S
  rw [hdiag, hoff, hswap]
  ring

theorem youngAdjacentOperator_swappable_eigen_plus {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentOperator a
        (fun S =>
          youngAdjacentOffCoeff T a * tableauBasisVec T S +
            (1 - youngAdjacentDiagCoeff T a) *
              tableauBasisVec (adjacentSwapTableau T a hrow_ne hcol_ne) S) =
      fun S =>
        youngAdjacentOffCoeff T a * tableauBasisVec T S +
          (1 - youngAdjacentDiagCoeff T a) *
            tableauBasisVec (adjacentSwapTableau T a hrow_ne hcol_ne) S := by
  let T' := adjacentSwapTableau T a hrow_ne hcol_ne
  let d := youngAdjacentDiagCoeff T a
  let o := youngAdjacentOffCoeff T a
  have hsq : d ^ 2 + o ^ 2 = 1 := by
    simpa [d, o] using youngAdjacentCoeff_sq_sum_of_swappable
      T a hrow_ne hcol_ne
  rw [youngAdjacentOperator_add, youngAdjacentOperator_smul,
    youngAdjacentOperator_smul]
  rw [youngAdjacentOperator_basis_swappable_eq T a hrow_ne hcol_ne,
    youngAdjacentOperator_basis_swappable_swap_eq T a hrow_ne hcol_ne]
  funext S
  let x := tableauBasisVec T S
  let y := tableauBasisVec T' S
  change
      o * (d * x + o * y) + (1 - d) * (o * x - d * y) =
        o * x + (1 - d) * y
  calc
    o * (d * x + o * y) + (1 - d) * (o * x - d * y)
        = o * x - d * y + (d ^ 2 + o ^ 2) * y := by ring
    _ = o * x - d * y + 1 * y := by rw [hsq]
    _ = o * x + (1 - d) * y := by ring

theorem youngAdjacentOperator_swappable_eigen_plus_ne_zero {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    (fun S =>
          youngAdjacentOffCoeff T a * tableauBasisVec T S +
            (1 - youngAdjacentDiagCoeff T a) *
              tableauBasisVec (adjacentSwapTableau T a hrow_ne hcol_ne) S)
      ≠ (0 : TableauSpace lam) := by
  let T' := adjacentSwapTableau T a hrow_ne hcol_ne
  have hT'_ne_T : T' ≠ T := by
    simpa [T'] using adjacentSwapTableau_ne_self T a hrow_ne hcol_ne
  intro hzero
  have hcoord := congrFun hzero T
  have hpos := youngAdjacentOffCoeff_pos_of_swappable T a hrow_ne hcol_ne
  rw [Pi.zero_apply] at hcoord
  rw [tableauBasisVec_self, tableauBasisVec_ne (Ne.symm hT'_ne_T)] at hcoord
  linarith

theorem youngAdjacentOperator_swappable_eigen_minus {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentOperator a
        (fun S =>
          youngAdjacentOffCoeff T a * tableauBasisVec T S -
            (1 + youngAdjacentDiagCoeff T a) *
              tableauBasisVec (adjacentSwapTableau T a hrow_ne hcol_ne) S) =
      fun S =>
        - (youngAdjacentOffCoeff T a * tableauBasisVec T S -
            (1 + youngAdjacentDiagCoeff T a) *
              tableauBasisVec (adjacentSwapTableau T a hrow_ne hcol_ne) S) := by
  let T' := adjacentSwapTableau T a hrow_ne hcol_ne
  let d := youngAdjacentDiagCoeff T a
  let o := youngAdjacentOffCoeff T a
  have hsq : d ^ 2 + o ^ 2 = 1 := by
    simpa [d, o] using youngAdjacentCoeff_sq_sum_of_swappable
      T a hrow_ne hcol_ne
  rw [show
      (fun S =>
        youngAdjacentOffCoeff T a * tableauBasisVec T S -
          (1 + youngAdjacentDiagCoeff T a) * tableauBasisVec T' S) =
        fun S =>
          youngAdjacentOffCoeff T a * tableauBasisVec T S +
            (-(1 + youngAdjacentDiagCoeff T a)) * tableauBasisVec T' S by
        funext S
        ring]
  rw [youngAdjacentOperator_add, youngAdjacentOperator_smul,
    youngAdjacentOperator_smul]
  rw [youngAdjacentOperator_basis_swappable_eq T a hrow_ne hcol_ne,
    youngAdjacentOperator_basis_swappable_swap_eq T a hrow_ne hcol_ne]
  funext S
  let x := tableauBasisVec T S
  let y := tableauBasisVec T' S
  change
      o * (d * x + o * y) + (-(1 + d)) * (o * x - d * y) =
        - (o * x - (1 + d) * y)
  calc
    o * (d * x + o * y) + (-(1 + d)) * (o * x - d * y)
        = -o * x + d * y + (d ^ 2 + o ^ 2) * y := by ring
    _ = -o * x + d * y + 1 * y := by rw [hsq]
    _ = - (o * x - (1 + d) * y) := by ring

theorem youngAdjacentOperator_swappable_eigen_minus_ne_zero {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    (fun S =>
          youngAdjacentOffCoeff T a * tableauBasisVec T S -
            (1 + youngAdjacentDiagCoeff T a) *
              tableauBasisVec (adjacentSwapTableau T a hrow_ne hcol_ne) S)
      ≠ (0 : TableauSpace lam) := by
  let T' := adjacentSwapTableau T a hrow_ne hcol_ne
  have hT'_ne_T : T' ≠ T := by
    simpa [T'] using adjacentSwapTableau_ne_self T a hrow_ne hcol_ne
  intro hzero
  have hcoord := congrFun hzero T
  have hpos := youngAdjacentOffCoeff_pos_of_swappable T a hrow_ne hcol_ne
  rw [Pi.zero_apply] at hcoord
  rw [tableauBasisVec_self, tableauBasisVec_ne (Ne.symm hT'_ne_T)] at hcoord
  linarith

noncomputable def youngAdjacentNeighbor {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) :
    StandardYoungTableau lam :=
  if hrow : adjacentSameRow T a then
    T
  else if hcol : adjacentSameCol T a then
    T
  else
    adjacentSwapTableau T a hrow hcol

theorem youngAdjacentOperator_basis_eq_diag_off_neighbor {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) :
    youngAdjacentOperator a (tableauBasisVec T) =
      fun S =>
        youngAdjacentDiagCoeff T a * tableauBasisVec T S +
          youngAdjacentOffCoeff T a *
            tableauBasisVec (youngAdjacentNeighbor T a) S := by
  by_cases hrow : adjacentSameRow T a
  · rw [youngAdjacentOperator_basis_sameRow T a hrow,
      youngAdjacentDiagCoeff_sameRow T a hrow,
      youngAdjacentOffCoeff_sameRow T a hrow]
    funext S
    simp [youngAdjacentNeighbor, hrow]
  · by_cases hcol : adjacentSameCol T a
    · rw [youngAdjacentOperator_basis_sameCol T a hcol,
        youngAdjacentDiagCoeff_sameCol T a hcol,
        youngAdjacentOffCoeff_sameCol T a hcol]
      funext S
      simp [youngAdjacentNeighbor, hrow, hcol]
    · rw [youngAdjacentOperator_basis_swappable_eq T a hrow hcol]
      funext S
      simp [youngAdjacentNeighbor, hrow, hcol]

theorem youngAdjacentOperator_sq_basis_swappable {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne :
      YoungCell.row (adjacentLoCell T a) ≠
        YoungCell.row (adjacentHiCell T a))
    (hcol_ne :
      YoungCell.col (adjacentLoCell T a) ≠
        YoungCell.col (adjacentHiCell T a)) :
    youngAdjacentOperator a
        (youngAdjacentOperator a (tableauBasisVec T)) =
      tableauBasisVec T := by
  let T' := adjacentSwapTableau T a hrow_ne hcol_ne
  let d := youngAdjacentDiagCoeff T a
  let o := youngAdjacentOffCoeff T a
  have hT'_ne_T : T' ≠ T := by
    simpa [T'] using adjacentSwapTableau_ne_self T a hrow_ne hcol_ne
  have hrow_ne' : ¬ adjacentSameRow T' a := by
    simpa [T'] using not_adjacentSameRow_swap T a hrow_ne hcol_ne
  have hcol_ne' : ¬ adjacentSameCol T' a := by
    simpa [T'] using not_adjacentSameCol_swap T a hrow_ne hcol_ne
  have hinv :
      adjacentSwapTableau T' a hrow_ne' hcol_ne' = T := by
    simpa [T'] using
      adjacentSwapTableau_involutive T a hrow_ne hcol_ne hrow_ne' hcol_ne'
  have hdiag :
      youngAdjacentDiagCoeff T' a = -d := by
    simpa [T', d] using youngAdjacentDiagCoeff_swap T a hrow_ne hcol_ne
  have hoff :
      youngAdjacentOffCoeff T' a = o := by
    simpa [T', o] using youngAdjacentOffCoeff_swap T a hrow_ne hcol_ne
  have hcoeff : d * d + o * o = 1 := by
    have h := youngAdjacentCoeff_sq_sum_of_swappable T a hrow_ne hcol_ne
    simpa [d, o, pow_two] using h
  rw [youngAdjacentOperator_basis_swappable_eq T a hrow_ne hcol_ne,
    youngAdjacentOperator_add,
    youngAdjacentOperator_smul,
    youngAdjacentOperator_smul,
    youngAdjacentOperator_basis_swappable_eq T a hrow_ne hcol_ne,
    youngAdjacentOperator_basis_swappable_eq T' a hrow_ne' hcol_ne']
  funext S
  rw [hdiag, hoff, hinv]
  simp only
  by_cases hST : S = T
  · subst S
    rw [tableauBasisVec_self, tableauBasisVec_ne hT'_ne_T.symm]
    nlinarith
  · by_cases hST' : S = T'
    · subst S
      rw [tableauBasisVec_ne hT'_ne_T, tableauBasisVec_self]
      ring
    · rw [tableauBasisVec_ne hST, tableauBasisVec_ne hST']
      ring

theorem youngAdjacentOperator_sq_basis {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) :
    youngAdjacentOperator a
        (youngAdjacentOperator a (tableauBasisVec T)) =
      tableauBasisVec T := by
  by_cases hrow : adjacentSameRow T a
  · exact youngAdjacentOperator_sq_basis_sameRow T a hrow
  · by_cases hcol : adjacentSameCol T a
    · exact youngAdjacentOperator_sq_basis_sameCol T a hcol
    · exact youngAdjacentOperator_sq_basis_swappable T a hrow hcol

theorem youngAdjacentOperator_sq_smul_basis {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) (c : ℝ) :
    youngAdjacentOperator a
        (youngAdjacentOperator a (fun S => c * tableauBasisVec T S)) =
      fun S => c * tableauBasisVec T S := by
  rw [youngAdjacentOperator_smul a c (tableauBasisVec T),
    youngAdjacentOperator_smul a c
      (youngAdjacentOperator a (tableauBasisVec T)),
    youngAdjacentOperator_sq_basis T a]

theorem youngAdjacentOperator_sq {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (a : Fin n) (f : TableauSpace lam) :
    youngAdjacentOperator a (youngAdjacentOperator a f) = f := by
  classical
  have hf := tableauBasis_expansion f
  calc
    youngAdjacentOperator a (youngAdjacentOperator a f)
        = youngAdjacentOperator a
            (youngAdjacentOperator a
              (fun S =>
                ∑ T : StandardYoungTableau lam,
                  f T * tableauBasisVec T S)) := by
            exact congrArg
              (fun g => youngAdjacentOperator a (youngAdjacentOperator a g))
              hf
    _ = youngAdjacentOperator a
          (fun S =>
            ∑ T : StandardYoungTableau lam,
              youngAdjacentOperator a
                (fun S => f T * tableauBasisVec T S) S) := by
            rw [youngAdjacentOperator_sum]
    _ = (fun S =>
          ∑ T : StandardYoungTableau lam,
            youngAdjacentOperator a
              (youngAdjacentOperator a
                (fun S => f T * tableauBasisVec T S)) S) := by
            rw [youngAdjacentOperator_sum]
    _ = (fun S =>
          ∑ T : StandardYoungTableau lam,
            f T * tableauBasisVec T S) := by
            funext S
            apply Finset.sum_congr rfl
            intro T _
            rw [youngAdjacentOperator_sq_smul_basis T a (f T)]
    _ = f := hf.symm

theorem youngAdjacentOperator_comm_basis_swappable_of_disjoint_indices
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hdisj : adjacentIndexDisjoint a b)
    (hrow_a :
      YoungCell.row (adjacentLoCell T a) ≠
        YoungCell.row (adjacentHiCell T a))
    (hcol_a :
      YoungCell.col (adjacentLoCell T a) ≠
        YoungCell.col (adjacentHiCell T a))
    (hrow_b :
      YoungCell.row (adjacentLoCell T b) ≠
        YoungCell.row (adjacentHiCell T b))
    (hcol_b :
      YoungCell.col (adjacentLoCell T b) ≠
        YoungCell.col (adjacentHiCell T b)) :
    youngAdjacentOperator a
        (youngAdjacentOperator b (tableauBasisVec T)) =
      youngAdjacentOperator b
        (youngAdjacentOperator a (tableauBasisVec T)) := by
  let Ta := adjacentSwapTableau T a hrow_a hcol_a
  let Tb := adjacentSwapTableau T b hrow_b hcol_b
  let hrow_a_after_b :
      YoungCell.row (adjacentLoCell Tb a) ≠
        YoungCell.row (adjacentHiCell Tb a) := by
    intro h
    exact hrow_a
      ((adjacentSameRow_after_disjoint_swap_iff T a b hdisj
        hrow_b hcol_b).1 (by simpa [Tb] using h))
  let hcol_a_after_b :
      YoungCell.col (adjacentLoCell Tb a) ≠
        YoungCell.col (adjacentHiCell Tb a) := by
    intro h
    exact hcol_a
      ((adjacentSameCol_after_disjoint_swap_iff T a b hdisj
        hrow_b hcol_b).1 (by simpa [Tb] using h))
  let hrow_b_after_a :
      YoungCell.row (adjacentLoCell Ta b) ≠
        YoungCell.row (adjacentHiCell Ta b) := by
    intro h
    exact hrow_b
      ((adjacentSameRow_after_disjoint_swap_iff T b a
        (adjacentIndexDisjoint_symm hdisj) hrow_a hcol_a).1
        (by simpa [Ta] using h))
  let hcol_b_after_a :
      YoungCell.col (adjacentLoCell Ta b) ≠
        YoungCell.col (adjacentHiCell Ta b) := by
    intro h
    exact hcol_b
      ((adjacentSameCol_after_disjoint_swap_iff T b a
        (adjacentIndexDisjoint_symm hdisj) hrow_a hcol_a).1
        (by simpa [Ta] using h))
  have hcomm :
      adjacentSwapTableau Tb a hrow_a_after_b hcol_a_after_b =
        adjacentSwapTableau Ta b hrow_b_after_a hcol_b_after_a := by
    exact adjacentSwapTableau_comm_of_disjoint_indices
      T a b hdisj hrow_a hcol_a hrow_b hcol_b
      hrow_a_after_b hcol_a_after_b hrow_b_after_a hcol_b_after_a
  have hdiag_a_Tb :
      youngAdjacentDiagCoeff Tb a = youngAdjacentDiagCoeff T a := by
    simpa [Tb] using
      youngAdjacentDiagCoeff_after_disjoint_swap_eq T a b hdisj
        hrow_b hcol_b
  have hoff_a_Tb :
      youngAdjacentOffCoeff Tb a = youngAdjacentOffCoeff T a := by
    simpa [Tb] using
      youngAdjacentOffCoeff_after_disjoint_swap_eq T a b hdisj
        hrow_b hcol_b
  have hdiag_b_Ta :
      youngAdjacentDiagCoeff Ta b = youngAdjacentDiagCoeff T b := by
    simpa [Ta] using
      youngAdjacentDiagCoeff_after_disjoint_swap_eq T b a
        (adjacentIndexDisjoint_symm hdisj) hrow_a hcol_a
  have hoff_b_Ta :
      youngAdjacentOffCoeff Ta b = youngAdjacentOffCoeff T b := by
    simpa [Ta] using
      youngAdjacentOffCoeff_after_disjoint_swap_eq T b a
        (adjacentIndexDisjoint_symm hdisj) hrow_a hcol_a
  have hleft :
      youngAdjacentOperator a
          (youngAdjacentOperator b (tableauBasisVec T)) =
        fun S =>
          youngAdjacentDiagCoeff T b *
              (youngAdjacentDiagCoeff T a * tableauBasisVec T S +
                youngAdjacentOffCoeff T a * tableauBasisVec Ta S) +
            youngAdjacentOffCoeff T b *
              (youngAdjacentDiagCoeff Tb a * tableauBasisVec Tb S +
                youngAdjacentOffCoeff Tb a *
                  tableauBasisVec
                    (adjacentSwapTableau Tb a hrow_a_after_b
                      hcol_a_after_b) S) := by
    rw [youngAdjacentOperator_basis_swappable_eq T b hrow_b hcol_b,
      youngAdjacentOperator_add, youngAdjacentOperator_smul,
      youngAdjacentOperator_smul,
      youngAdjacentOperator_basis_swappable_eq T a hrow_a hcol_a,
      youngAdjacentOperator_basis_swappable_eq Tb a hrow_a_after_b
        hcol_a_after_b]
  have hright :
      youngAdjacentOperator b
          (youngAdjacentOperator a (tableauBasisVec T)) =
        fun S =>
          youngAdjacentDiagCoeff T a *
              (youngAdjacentDiagCoeff T b * tableauBasisVec T S +
                youngAdjacentOffCoeff T b * tableauBasisVec Tb S) +
            youngAdjacentOffCoeff T a *
              (youngAdjacentDiagCoeff Ta b * tableauBasisVec Ta S +
                youngAdjacentOffCoeff Ta b *
                  tableauBasisVec
                    (adjacentSwapTableau Ta b hrow_b_after_a
                      hcol_b_after_a) S) := by
    rw [youngAdjacentOperator_basis_swappable_eq T a hrow_a hcol_a,
      youngAdjacentOperator_add, youngAdjacentOperator_smul,
      youngAdjacentOperator_smul,
      youngAdjacentOperator_basis_swappable_eq T b hrow_b hcol_b,
      youngAdjacentOperator_basis_swappable_eq Ta b hrow_b_after_a
        hcol_b_after_a]
  rw [hleft, hright]
  funext S
  rw [hdiag_a_Tb, hoff_a_Tb, hdiag_b_Ta, hoff_b_Ta, hcomm]
  ring

theorem youngAdjacentOperator_comm_basis_left_sameRow_of_disjoint_indices
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hdisj : adjacentIndexDisjoint a b)
    (hrow_a : adjacentSameRow T a) :
    youngAdjacentOperator a
        (youngAdjacentOperator b (tableauBasisVec T)) =
      youngAdjacentOperator b
        (youngAdjacentOperator a (tableauBasisVec T)) := by
  rw [youngAdjacentOperator_basis_sameRow T a hrow_a]
  by_cases hrow_b : adjacentSameRow T b
  · rw [youngAdjacentOperator_basis_sameRow T b hrow_b,
      youngAdjacentOperator_basis_sameRow T a hrow_a]
  · by_cases hcol_b : adjacentSameCol T b
    · rw [youngAdjacentOperator_basis_sameCol T b hcol_b,
        youngAdjacentOperator_neg,
        youngAdjacentOperator_basis_sameRow T a hrow_a]
    · let Tb := adjacentSwapTableau T b hrow_b hcol_b
      have hrow_a_after_b : adjacentSameRow Tb a := by
        exact (adjacentSameRow_after_disjoint_swap_iff T a b hdisj
          hrow_b hcol_b).2 hrow_a
      rw [youngAdjacentOperator_basis_swappable_eq T b hrow_b hcol_b,
        youngAdjacentOperator_add, youngAdjacentOperator_smul,
        youngAdjacentOperator_smul,
        youngAdjacentOperator_basis_sameRow T a hrow_a,
        youngAdjacentOperator_basis_sameRow Tb a hrow_a_after_b]

theorem youngAdjacentOperator_comm_basis_left_sameCol_of_disjoint_indices
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hdisj : adjacentIndexDisjoint a b)
    (hcol_a : adjacentSameCol T a) :
    youngAdjacentOperator a
        (youngAdjacentOperator b (tableauBasisVec T)) =
      youngAdjacentOperator b
        (youngAdjacentOperator a (tableauBasisVec T)) := by
  by_cases hrow_b : adjacentSameRow T b
  · rw [youngAdjacentOperator_basis_sameRow T b hrow_b,
      youngAdjacentOperator_basis_sameCol T a hcol_a,
      youngAdjacentOperator_neg,
      youngAdjacentOperator_basis_sameRow T b hrow_b]
  · by_cases hcol_b : adjacentSameCol T b
    · rw [youngAdjacentOperator_basis_sameCol T b hcol_b,
        youngAdjacentOperator_neg,
        youngAdjacentOperator_basis_sameCol T a hcol_a,
        youngAdjacentOperator_neg,
        youngAdjacentOperator_basis_sameCol T b hcol_b]
    · let Tb := adjacentSwapTableau T b hrow_b hcol_b
      have hcol_a_after_b : adjacentSameCol Tb a := by
        exact (adjacentSameCol_after_disjoint_swap_iff T a b hdisj
          hrow_b hcol_b).2 hcol_a
      rw [youngAdjacentOperator_basis_swappable_eq T b hrow_b hcol_b,
        youngAdjacentOperator_add, youngAdjacentOperator_smul,
        youngAdjacentOperator_smul,
        youngAdjacentOperator_basis_sameCol T a hcol_a,
        youngAdjacentOperator_basis_sameCol Tb a hcol_a_after_b]
      rw [youngAdjacentOperator_neg,
      youngAdjacentOperator_basis_swappable_eq T b hrow_b hcol_b]
      funext S
      ring

theorem youngAdjacentOperator_comm_basis_of_disjoint_indices
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hdisj : adjacentIndexDisjoint a b) :
    youngAdjacentOperator a
        (youngAdjacentOperator b (tableauBasisVec T)) =
      youngAdjacentOperator b
        (youngAdjacentOperator a (tableauBasisVec T)) := by
  by_cases hrow_a : adjacentSameRow T a
  · exact youngAdjacentOperator_comm_basis_left_sameRow_of_disjoint_indices
      T a b hdisj hrow_a
  · by_cases hcol_a : adjacentSameCol T a
    · exact youngAdjacentOperator_comm_basis_left_sameCol_of_disjoint_indices
        T a b hdisj hcol_a
    · by_cases hrow_b : adjacentSameRow T b
      · exact (youngAdjacentOperator_comm_basis_left_sameRow_of_disjoint_indices
          T b a (adjacentIndexDisjoint_symm hdisj) hrow_b).symm
      · by_cases hcol_b : adjacentSameCol T b
        · exact (youngAdjacentOperator_comm_basis_left_sameCol_of_disjoint_indices
            T b a (adjacentIndexDisjoint_symm hdisj) hcol_b).symm
        · exact youngAdjacentOperator_comm_basis_swappable_of_disjoint_indices
            T a b hdisj hrow_a hcol_a hrow_b hcol_b

theorem youngAdjacentOperator_comm_smul_basis_of_disjoint_indices
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hdisj : adjacentIndexDisjoint a b) (c : ℝ) :
    youngAdjacentOperator a
        (youngAdjacentOperator b (fun S => c * tableauBasisVec T S)) =
      youngAdjacentOperator b
        (youngAdjacentOperator a (fun S => c * tableauBasisVec T S)) := by
  rw [youngAdjacentOperator_smul b c (tableauBasisVec T),
    youngAdjacentOperator_smul a c (tableauBasisVec T),
    youngAdjacentOperator_smul a c
      (youngAdjacentOperator b (tableauBasisVec T)),
    youngAdjacentOperator_smul b c
      (youngAdjacentOperator a (tableauBasisVec T)),
    youngAdjacentOperator_comm_basis_of_disjoint_indices T a b hdisj]

theorem youngAdjacentOperator_comm_of_disjoint_indices
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (a b : Fin n) (hdisj : adjacentIndexDisjoint a b)
    (f : TableauSpace lam) :
    youngAdjacentOperator a (youngAdjacentOperator b f) =
      youngAdjacentOperator b (youngAdjacentOperator a f) := by
  classical
  have hf := tableauBasis_expansion f
  calc
    youngAdjacentOperator a (youngAdjacentOperator b f)
        = youngAdjacentOperator a
            (youngAdjacentOperator b
              (fun S =>
                ∑ T : StandardYoungTableau lam,
                  f T * tableauBasisVec T S)) := by
            exact congrArg
              (fun g => youngAdjacentOperator a (youngAdjacentOperator b g))
              hf
    _ = youngAdjacentOperator a
          (fun S =>
            ∑ T : StandardYoungTableau lam,
              youngAdjacentOperator b
                (fun S => f T * tableauBasisVec T S) S) := by
            rw [youngAdjacentOperator_sum]
    _ = (fun S =>
          ∑ T : StandardYoungTableau lam,
            youngAdjacentOperator a
              (youngAdjacentOperator b
                (fun S => f T * tableauBasisVec T S)) S) := by
            rw [youngAdjacentOperator_sum]
    _ = (fun S =>
          ∑ T : StandardYoungTableau lam,
            youngAdjacentOperator b
              (youngAdjacentOperator a
                (fun S => f T * tableauBasisVec T S)) S) := by
            funext S
            apply Finset.sum_congr rfl
            intro T _
            rw [youngAdjacentOperator_comm_smul_basis_of_disjoint_indices
              T a b hdisj (f T)]
    _ = youngAdjacentOperator b
          (fun S =>
            ∑ T : StandardYoungTableau lam,
              youngAdjacentOperator a
                (fun S => f T * tableauBasisVec T S) S) := by
            rw [← youngAdjacentOperator_sum]
    _ = youngAdjacentOperator b
          (youngAdjacentOperator a
            (fun S =>
              ∑ T : StandardYoungTableau lam,
                f T * tableauBasisVec T S)) := by
            rw [← youngAdjacentOperator_sum]
    _ = youngAdjacentOperator b (youngAdjacentOperator a f) := by
            exact congrArg
              (fun g => youngAdjacentOperator b (youngAdjacentOperator a g))
              hf.symm

theorem youngAdjacentOperator_braid_basis_swappable_of_succ
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hsucc : (b : Nat) = (a : Nat) + 1)
    (hrow_a : ¬ adjacentSameRow T a)
    (hcol_a : ¬ adjacentSameCol T a)
    (hrow_b : ¬ adjacentSameRow T b)
    (hcol_b : ¬ adjacentSameCol T b)
    (hrow_b_after_a :
      ¬ adjacentSameRow (adjacentSwapTableau T a hrow_a hcol_a) b)
    (hcol_b_after_a :
      ¬ adjacentSameCol (adjacentSwapTableau T a hrow_a hcol_a) b)
    (hrow_a_after_b_after_a :
      ¬ adjacentSameRow
        (adjacentSwapTableau
          (adjacentSwapTableau T a hrow_a hcol_a) b
          hrow_b_after_a hcol_b_after_a) a)
    (hcol_a_after_b_after_a :
      ¬ adjacentSameCol
        (adjacentSwapTableau
          (adjacentSwapTableau T a hrow_a hcol_a) b
          hrow_b_after_a hcol_b_after_a) a)
    (hrow_a_after_b :
      ¬ adjacentSameRow (adjacentSwapTableau T b hrow_b hcol_b) a)
    (hcol_a_after_b :
      ¬ adjacentSameCol (adjacentSwapTableau T b hrow_b hcol_b) a)
    (hrow_b_after_a_after_b :
      ¬ adjacentSameRow
        (adjacentSwapTableau
          (adjacentSwapTableau T b hrow_b hcol_b) a
          hrow_a_after_b hcol_a_after_b) b)
    (hcol_b_after_a_after_b :
      ¬ adjacentSameCol
        (adjacentSwapTableau
          (adjacentSwapTableau T b hrow_b hcol_b) a
          hrow_a_after_b hcol_a_after_b) b) :
    youngAdjacentOperator a
        (youngAdjacentOperator b
          (youngAdjacentOperator a (tableauBasisVec T))) =
      youngAdjacentOperator b
        (youngAdjacentOperator a
          (youngAdjacentOperator b (tableauBasisVec T))) := by
  let Ta := adjacentSwapTableau T a hrow_a hcol_a
  let Tb := adjacentSwapTableau T b hrow_b hcol_b
  let Tab := adjacentSwapTableau Ta b hrow_b_after_a hcol_b_after_a
  let Tba := adjacentSwapTableau Tb a hrow_a_after_b hcol_a_after_b
  let Taba :=
    adjacentSwapTableau Tab a hrow_a_after_b_after_a
      hcol_a_after_b_after_a
  let Tbab :=
    adjacentSwapTableau Tba b hrow_b_after_a_after_b
      hcol_b_after_a_after_b
  let da := youngAdjacentDiagCoeff T a
  let db := youngAdjacentDiagCoeff T b
  let dz := youngAdjacentDiagCoeff Ta b
  let oa := youngAdjacentOffCoeff T a
  let ob := youngAdjacentOffCoeff T b
  let oz := youngAdjacentOffCoeff Ta b
  have hrow_a_after_a : ¬ adjacentSameRow Ta a := by
    simpa [Ta] using not_adjacentSameRow_swap T a hrow_a hcol_a
  have hcol_a_after_a : ¬ adjacentSameCol Ta a := by
    simpa [Ta] using not_adjacentSameCol_swap T a hrow_a hcol_a
  have hrow_b_after_b : ¬ adjacentSameRow Tb b := by
    simpa [Tb] using not_adjacentSameRow_swap T b hrow_b hcol_b
  have hcol_b_after_b : ¬ adjacentSameCol Tb b := by
    simpa [Tb] using not_adjacentSameCol_swap T b hrow_b hcol_b
  have hinv_a :
      adjacentSwapTableau Ta a hrow_a_after_a hcol_a_after_a = T := by
    simpa [Ta] using
      adjacentSwapTableau_involutive T a hrow_a hcol_a
        hrow_a_after_a hcol_a_after_a
  have hinv_b :
      adjacentSwapTableau Tb b hrow_b_after_b hcol_b_after_b = T := by
    simpa [Tb] using
      adjacentSwapTableau_involutive T b hrow_b hcol_b
        hrow_b_after_b hcol_b_after_b
  have hbraid : Taba = Tbab := by
    simpa [Ta, Tb, Tab, Tba, Taba, Tbab] using
      adjacentSwapTableau_braid_of_succ T a b hsucc
        hrow_a hcol_a hrow_b_after_a hcol_b_after_a
        hrow_a_after_b_after_a hcol_a_after_b_after_a
        hrow_b hcol_b hrow_a_after_b hcol_a_after_b
        hrow_b_after_a_after_b hcol_b_after_a_after_b
  have hdiag_Ta_a : youngAdjacentDiagCoeff Ta a = -da := by
    simpa [Ta, da] using youngAdjacentDiagCoeff_swap T a hrow_a hcol_a
  have hoff_Ta_a : youngAdjacentOffCoeff Ta a = oa := by
    simpa [Ta, oa] using youngAdjacentOffCoeff_swap T a hrow_a hcol_a
  have hdiag_Tb_b : youngAdjacentDiagCoeff Tb b = -db := by
    simpa [Tb, db] using youngAdjacentDiagCoeff_swap T b hrow_b hcol_b
  have hoff_Tb_b : youngAdjacentOffCoeff Tb b = ob := by
    simpa [Tb, ob] using youngAdjacentOffCoeff_swap T b hrow_b hcol_b
  have hdiag_Tb_a : youngAdjacentDiagCoeff Tb a = dz := by
    simpa [Ta, Tb, dz] using
      (youngAdjacentDiagCoeff_after_left_swap_eq_after_right_swap_of_succ
        T a b hsucc hrow_a hcol_a hrow_b hcol_b).symm
  have hoff_Tb_a : youngAdjacentOffCoeff Tb a = oz := by
    simpa [Ta, Tb, oz] using
      (youngAdjacentOffCoeff_after_left_swap_eq_after_right_swap_of_succ
        T a b hsucc hrow_a hcol_a hrow_b hcol_b).symm
  have hdiag_Tab_a : youngAdjacentDiagCoeff Tab a = db := by
    simpa [Ta, Tab, db] using
      youngAdjacentDiagCoeff_after_left_right_swap_of_succ
        T a b hsucc hrow_a hcol_a hrow_b_after_a hcol_b_after_a
  have hoff_Tab_a : youngAdjacentOffCoeff Tab a = ob := by
    simpa [Ta, Tab, ob] using
      youngAdjacentOffCoeff_after_left_right_swap_of_succ
        T a b hsucc hrow_a hcol_a hrow_b_after_a hcol_b_after_a
  have hdiag_Tba_b : youngAdjacentDiagCoeff Tba b = da := by
    simpa [Tb, Tba, da] using
      youngAdjacentDiagCoeff_after_right_left_swap_of_succ
        T a b hsucc hrow_b hcol_b hrow_a_after_b hcol_a_after_b
  have hoff_Tba_b : youngAdjacentOffCoeff Tba b = oa := by
    simpa [Tb, Tba, oa] using
      youngAdjacentOffCoeff_after_right_left_swap_of_succ
        T a b hsucc hrow_b hcol_b hrow_a_after_b hcol_a_after_b
  let x : ℝ := (adjacentAxialDistance T a : ℝ)
  let y : ℝ := (adjacentAxialDistance T b : ℝ)
  let z : ℝ := ((adjacentAxialDistance T a +
    adjacentAxialDistance T b : Int) : ℝ)
  have hx : x ≠ 0 := by
    have hx_int := adjacentAxialDistance_ne_zero_of_swappable
      T a hrow_a hcol_a
    have hx_real : ((adjacentAxialDistance T a : ℝ) ≠ 0) := by
      exact_mod_cast hx_int
    simpa [x] using hx_real
  have hy : y ≠ 0 := by
    have hy_int := adjacentAxialDistance_ne_zero_of_swappable
      T b hrow_b hcol_b
    have hy_real : ((adjacentAxialDistance T b : ℝ) ≠ 0) := by
      exact_mod_cast hy_int
    simpa [y] using hy_real
  have hz0 : z ≠ 0 := by
    have hz_int := adjacentAxialDistance_ne_zero_of_swappable
      Ta b hrow_b_after_a hcol_b_after_a
    have hz_real : ((adjacentAxialDistance Ta b : ℝ) ≠ 0) := by
      exact_mod_cast hz_int
    have hsum_real : ((adjacentAxialDistance Ta b : ℝ)) = z := by
      simpa [Ta, z] using congrArg (fun m : Int => (m : ℝ))
        (adjacentAxialDistance_after_left_swap_of_succ
          T a b hsucc hrow_a hcol_a)
    rwa [hsum_real] at hz_real
  have hsum : z = x + y := by
    simp [x, y, z]
  have hdz : dz = z⁻¹ := by
    simpa [Ta, dz, z] using
      youngAdjacentDiagCoeff_after_left_swap_of_succ
        T a b hsucc hrow_a hcol_a
  have hTa_coeff : da * (db - dz) = db * dz := by
    have h := inv_braid_left_identity hx hy hz0 hsum
    simpa [da, db, dz, x, y, z, hdz, youngAdjacentDiagCoeff]
      using h
  have hTb_coeff : db * (da - dz) = da * dz := by
    have h := inv_braid_right_identity hx hy hz0 hsum
    simpa [da, db, dz, x, y, z, hdz, youngAdjacentDiagCoeff]
      using h
  have hcoeff_a : da ^ 2 + oa ^ 2 = 1 := by
    simpa [da, oa] using
      youngAdjacentCoeff_sq_sum_of_swappable T a hrow_a hcol_a
  have hcoeff_b : db ^ 2 + ob ^ 2 = 1 := by
    simpa [db, ob] using
      youngAdjacentCoeff_sq_sum_of_swappable T b hrow_b hcol_b
  have hoa_sq : oa ^ 2 = 1 - da ^ 2 := by
    nlinarith
  have hob_sq : ob ^ 2 = 1 - db ^ 2 := by
    nlinarith
  have hT_inv :
      da ^ 2 * db + (1 - da ^ 2) * dz =
        db ^ 2 * da + (1 - db ^ 2) * dz := by
    have h := inv_sq_braid_diag_identity hx hy hz0 hsum
    simpa [da, db, dz, x, y, z, hdz, youngAdjacentDiagCoeff]
      using h
  have hT_coeff :
      da ^ 2 * db + oa ^ 2 * dz =
        db ^ 2 * da + ob ^ 2 * dz := by
    rw [hoa_sq, hob_sq]
    exact hT_inv
  have hleft :
      youngAdjacentOperator a
          (youngAdjacentOperator b
            (youngAdjacentOperator a (tableauBasisVec T))) =
        fun S =>
          da * (db * (da * tableauBasisVec T S +
                oa * tableauBasisVec Ta S) +
              ob * (dz * tableauBasisVec Tb S +
                oz * tableauBasisVec Tba S)) +
            oa * (dz * ((-da) * tableauBasisVec Ta S +
                oa * tableauBasisVec T S) +
              oz * (db * tableauBasisVec Tab S +
                ob * tableauBasisVec Taba S)) := by
    rw [youngAdjacentOperator_basis_swappable_eq T a hrow_a hcol_a,
      youngAdjacentOperator_add, youngAdjacentOperator_smul,
      youngAdjacentOperator_smul,
      youngAdjacentOperator_basis_swappable_eq T b hrow_b hcol_b,
      youngAdjacentOperator_basis_swappable_eq Ta b hrow_b_after_a
        hcol_b_after_a,
      youngAdjacentOperator_add, youngAdjacentOperator_smul,
      youngAdjacentOperator_smul,
      youngAdjacentOperator_add, youngAdjacentOperator_smul,
      youngAdjacentOperator_smul,
      youngAdjacentOperator_basis_swappable_eq T a hrow_a hcol_a,
      youngAdjacentOperator_basis_swappable_eq Tb a hrow_a_after_b
        hcol_a_after_b,
      youngAdjacentOperator_add, youngAdjacentOperator_smul,
      youngAdjacentOperator_smul,
      youngAdjacentOperator_basis_swappable_eq Ta a hrow_a_after_a
        hcol_a_after_a,
      youngAdjacentOperator_basis_swappable_eq Tab a
        hrow_a_after_b_after_a hcol_a_after_b_after_a]
    funext S
    rw [hdiag_Tb_a, hoff_Tb_a, hdiag_Ta_a, hoff_Ta_a, hinv_a,
      hdiag_Tab_a, hoff_Tab_a]
  have hright :
      youngAdjacentOperator b
          (youngAdjacentOperator a
            (youngAdjacentOperator b (tableauBasisVec T))) =
        fun S =>
          db * (da * (db * tableauBasisVec T S +
                ob * tableauBasisVec Tb S) +
              oa * (dz * tableauBasisVec Ta S +
                oz * tableauBasisVec Tab S)) +
            ob * (dz * ((-db) * tableauBasisVec Tb S +
                ob * tableauBasisVec T S) +
              oz * (da * tableauBasisVec Tba S +
                oa * tableauBasisVec Tbab S)) := by
    rw [youngAdjacentOperator_basis_swappable_eq T b hrow_b hcol_b,
      youngAdjacentOperator_add, youngAdjacentOperator_smul,
      youngAdjacentOperator_smul,
      youngAdjacentOperator_basis_swappable_eq T a hrow_a hcol_a,
      youngAdjacentOperator_basis_swappable_eq Tb a hrow_a_after_b
        hcol_a_after_b,
      youngAdjacentOperator_add, youngAdjacentOperator_smul,
      youngAdjacentOperator_smul,
      youngAdjacentOperator_add, youngAdjacentOperator_smul,
      youngAdjacentOperator_smul,
      youngAdjacentOperator_basis_swappable_eq T b hrow_b hcol_b,
      youngAdjacentOperator_basis_swappable_eq Ta b hrow_b_after_a
        hcol_b_after_a,
      youngAdjacentOperator_add, youngAdjacentOperator_smul,
      youngAdjacentOperator_smul,
      youngAdjacentOperator_basis_swappable_eq Tb b hrow_b_after_b
        hcol_b_after_b,
      youngAdjacentOperator_basis_swappable_eq Tba b
        hrow_b_after_a_after_b hcol_b_after_a_after_b]
    funext S
    rw [hdiag_Tb_a, hoff_Tb_a, hdiag_Tb_b, hoff_Tb_b, hinv_b,
      hdiag_Tba_b, hoff_Tba_b]
  rw [hleft, hright]
  funext S
  rw [hbraid]
  exact braid_six_coefficient_identity da db dz oa ob oz
    (tableauBasisVec T S) (tableauBasisVec Ta S)
    (tableauBasisVec Tb S) (tableauBasisVec Tab S)
    (tableauBasisVec Tba S) (tableauBasisVec Tbab S)
    hT_coeff hTa_coeff hTb_coeff

theorem youngAdjacentOperator_braid_basis_sameRow_sameRow_of_succ
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (_hsucc : (b : Nat) = (a : Nat) + 1)
    (hrow_a : adjacentSameRow T a)
    (hrow_b : adjacentSameRow T b) :
    youngAdjacentOperator a
        (youngAdjacentOperator b
          (youngAdjacentOperator a (tableauBasisVec T))) =
      youngAdjacentOperator b
        (youngAdjacentOperator a
          (youngAdjacentOperator b (tableauBasisVec T))) := by
  calc
    youngAdjacentOperator a
        (youngAdjacentOperator b
          (youngAdjacentOperator a (tableauBasisVec T))) =
        tableauBasisVec T := by
          rw [youngAdjacentOperator_basis_sameRow T a hrow_a,
            youngAdjacentOperator_basis_sameRow T b hrow_b,
            youngAdjacentOperator_basis_sameRow T a hrow_a]
    _ = youngAdjacentOperator b
        (youngAdjacentOperator a
          (youngAdjacentOperator b (tableauBasisVec T))) := by
          rw [youngAdjacentOperator_basis_sameRow T b hrow_b,
            youngAdjacentOperator_basis_sameRow T a hrow_a,
            youngAdjacentOperator_basis_sameRow T b hrow_b]

theorem youngAdjacentOperator_braid_basis_sameCol_sameCol_of_succ
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (_hsucc : (b : Nat) = (a : Nat) + 1)
    (hcol_a : adjacentSameCol T a)
    (hcol_b : adjacentSameCol T b) :
    youngAdjacentOperator a
        (youngAdjacentOperator b
          (youngAdjacentOperator a (tableauBasisVec T))) =
      youngAdjacentOperator b
        (youngAdjacentOperator a
          (youngAdjacentOperator b (tableauBasisVec T))) := by
  have ha_neg :
      youngAdjacentOperator a (fun S => -tableauBasisVec T S) =
        tableauBasisVec T := by
    rw [youngAdjacentOperator_neg,
      youngAdjacentOperator_basis_sameCol T a hcol_a]
    funext S
    simp
  have hb_neg :
      youngAdjacentOperator b (fun S => -tableauBasisVec T S) =
        tableauBasisVec T := by
    rw [youngAdjacentOperator_neg,
      youngAdjacentOperator_basis_sameCol T b hcol_b]
    funext S
    simp
  calc
    youngAdjacentOperator a
        (youngAdjacentOperator b
          (youngAdjacentOperator a (tableauBasisVec T))) =
        youngAdjacentOperator a
          (youngAdjacentOperator b (fun S => -tableauBasisVec T S)) := by
          rw [youngAdjacentOperator_basis_sameCol T a hcol_a]
    _ = youngAdjacentOperator a (tableauBasisVec T) := by
          rw [hb_neg]
    _ = (fun S => -tableauBasisVec T S) := by
          rw [youngAdjacentOperator_basis_sameCol T a hcol_a]
    _ = youngAdjacentOperator b
        (youngAdjacentOperator a
          (youngAdjacentOperator b (tableauBasisVec T))) := by
          rw [youngAdjacentOperator_basis_sameCol T b hcol_b,
            ha_neg,
            youngAdjacentOperator_basis_sameCol T b hcol_b]

theorem youngAdjacentOperator_braid_basis_left_sameRow_right_swappable_of_succ
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hsucc : (b : Nat) = (a : Nat) + 1)
    (hrow_a : adjacentSameRow T a)
    (hrow_b : ¬ adjacentSameRow T b)
    (hcol_b : ¬ adjacentSameCol T b) :
    youngAdjacentOperator a
        (youngAdjacentOperator b
          (youngAdjacentOperator a (tableauBasisVec T))) =
      youngAdjacentOperator b
        (youngAdjacentOperator a
          (youngAdjacentOperator b (tableauBasisVec T))) := by
  let Tb := adjacentSwapTableau T b hrow_b hcol_b
  let db := youngAdjacentDiagCoeff T b
  let ob := youngAdjacentOffCoeff T b
  have hrow_a_after_b : ¬ adjacentSameRow Tb a := by
    simpa [Tb] using
      not_adjacentSameRow_after_right_swap_of_left_sameRow_of_succ
        T a b hsucc hrow_a hrow_b hcol_b
  have hrow_b_after_b : ¬ adjacentSameRow Tb b := by
    simpa [Tb] using not_adjacentSameRow_swap T b hrow_b hcol_b
  have hcol_b_after_b : ¬ adjacentSameCol Tb b := by
    simpa [Tb] using not_adjacentSameCol_swap T b hrow_b hcol_b
  have hinv_b :
      adjacentSwapTableau Tb b hrow_b_after_b hcol_b_after_b = T := by
    simpa [Tb] using
      adjacentSwapTableau_involutive T b hrow_b hcol_b
        hrow_b_after_b hcol_b_after_b
  have hdiag_Tb_b : youngAdjacentDiagCoeff Tb b = -db := by
    simpa [Tb, db] using youngAdjacentDiagCoeff_swap T b hrow_b hcol_b
  have hoff_Tb_b : youngAdjacentOffCoeff Tb b = ob := by
    simpa [Tb, ob] using youngAdjacentOffCoeff_swap T b hrow_b hcol_b
  have hcoeff_b : db ^ 2 + ob ^ 2 = 1 := by
    simpa [db, ob] using
      youngAdjacentCoeff_sq_sum_of_swappable T b hrow_b hcol_b
  by_cases hcol_a_after_b : adjacentSameCol Tb a
  · have hdist_b : adjacentAxialDistance T b = -2 := by
      have hafter :
          adjacentAxialDistance Tb a =
            adjacentAxialDistance T a + adjacentAxialDistance T b := by
        simpa [Tb] using
          adjacentAxialDistance_after_right_swap_of_succ
            T a b hsucc hrow_b hcol_b
      have ha := adjacentAxialDistance_sameRow T a hrow_a
      have hafter_col := adjacentAxialDistance_sameCol Tb a hcol_a_after_b
      omega
    have hdb : db = -(1 / 2 : ℝ) := by
      change youngAdjacentDiagCoeff T b = -(1 / 2 : ℝ)
      rw [youngAdjacentDiagCoeff, hdist_b]
      norm_num
    have hT_coeff : db ^ 2 - ob ^ 2 = db := by
      nlinarith
    have hTb_coeff : db * ob + ob * db = -ob := by
      nlinarith
    have hleft :
        youngAdjacentOperator a
            (youngAdjacentOperator b
              (youngAdjacentOperator a (tableauBasisVec T))) =
          fun S => db * tableauBasisVec T S - ob * tableauBasisVec Tb S := by
      rw [youngAdjacentOperator_basis_sameRow T a hrow_a,
        youngAdjacentOperator_basis_swappable_eq T b hrow_b hcol_b,
        youngAdjacentOperator_add, youngAdjacentOperator_smul,
        youngAdjacentOperator_smul,
        youngAdjacentOperator_basis_sameRow T a hrow_a,
        youngAdjacentOperator_basis_sameCol Tb a hcol_a_after_b]
      funext S
      ring
    have hright :
        youngAdjacentOperator b
            (youngAdjacentOperator a
              (youngAdjacentOperator b (tableauBasisVec T))) =
          fun S =>
            (db ^ 2 - ob ^ 2) * tableauBasisVec T S +
              (db * ob + ob * db) * tableauBasisVec Tb S := by
      rw [youngAdjacentOperator_basis_swappable_eq T b hrow_b hcol_b,
        youngAdjacentOperator_add, youngAdjacentOperator_smul,
        youngAdjacentOperator_smul,
        youngAdjacentOperator_basis_sameRow T a hrow_a,
        youngAdjacentOperator_basis_sameCol Tb a hcol_a_after_b,
        youngAdjacentOperator_add, youngAdjacentOperator_smul,
        youngAdjacentOperator_smul,
        youngAdjacentOperator_basis_swappable_eq T b hrow_b hcol_b,
        youngAdjacentOperator_neg,
        youngAdjacentOperator_basis_swappable_eq Tb b hrow_b_after_b
          hcol_b_after_b]
      funext S
      rw [hdiag_Tb_b, hoff_Tb_b, hinv_b]
      ring
    rw [hleft, hright]
    funext S
    rw [hT_coeff, hTb_coeff]
    ring
  · let Tba := adjacentSwapTableau Tb a hrow_a_after_b hcol_a_after_b
    let dz := youngAdjacentDiagCoeff Tb a
    let oz := youngAdjacentOffCoeff Tb a
    have hdiag_Tba_b : youngAdjacentDiagCoeff Tba b = 1 := by
      have hdist :
          adjacentAxialDistance Tba b = 1 := by
        have hdist0 :
            adjacentAxialDistance Tba b = adjacentAxialDistance T a := by
          simpa [Tb, Tba] using
            adjacentAxialDistance_after_right_left_swap_of_succ
              T a b hsucc hrow_b hcol_b hrow_a_after_b hcol_a_after_b
        have ha := adjacentAxialDistance_sameRow T a hrow_a
        omega
      rw [youngAdjacentDiagCoeff, hdist]
      norm_num
    have hrow_b_after_a_after_b : adjacentSameRow Tba b := by
      apply adjacentSameRow_of_axialDistance_eq_one
      simpa [youngAdjacentDiagCoeff] using hdiag_Tba_b
    have hleft :
        youngAdjacentOperator a
            (youngAdjacentOperator b
              (youngAdjacentOperator a (tableauBasisVec T))) =
          fun S =>
            db * tableauBasisVec T S +
              ob * (dz * tableauBasisVec Tb S +
                oz * tableauBasisVec Tba S) := by
      rw [youngAdjacentOperator_basis_sameRow T a hrow_a,
        youngAdjacentOperator_basis_swappable_eq T b hrow_b hcol_b,
        youngAdjacentOperator_add, youngAdjacentOperator_smul,
        youngAdjacentOperator_smul,
        youngAdjacentOperator_basis_sameRow T a hrow_a,
        youngAdjacentOperator_basis_swappable_eq Tb a hrow_a_after_b
          hcol_a_after_b]
    have hright :
        youngAdjacentOperator b
            (youngAdjacentOperator a
              (youngAdjacentOperator b (tableauBasisVec T))) =
          fun S =>
            (db ^ 2 + ob ^ 2 * dz) * tableauBasisVec T S +
              (db * ob - ob * dz * db) * tableauBasisVec Tb S +
              ob * oz * tableauBasisVec Tba S := by
      rw [youngAdjacentOperator_basis_swappable_eq T b hrow_b hcol_b,
        youngAdjacentOperator_add, youngAdjacentOperator_smul,
        youngAdjacentOperator_smul,
        youngAdjacentOperator_basis_sameRow T a hrow_a,
        youngAdjacentOperator_basis_swappable_eq Tb a hrow_a_after_b
          hcol_a_after_b,
        youngAdjacentOperator_add, youngAdjacentOperator_smul,
        youngAdjacentOperator_smul,
        youngAdjacentOperator_basis_swappable_eq T b hrow_b hcol_b,
        youngAdjacentOperator_add, youngAdjacentOperator_smul,
        youngAdjacentOperator_smul,
        youngAdjacentOperator_basis_swappable_eq Tb b hrow_b_after_b
          hcol_b_after_b,
        youngAdjacentOperator_basis_sameRow Tba b hrow_b_after_a_after_b]
      funext S
      rw [hdiag_Tb_b, hoff_Tb_b, hinv_b]
      ring
    have hdist_after :
        adjacentAxialDistance Tb a =
          1 + adjacentAxialDistance T b := by
      have hafter :
          adjacentAxialDistance Tb a =
            adjacentAxialDistance T a + adjacentAxialDistance T b := by
        simpa [Tb] using
          adjacentAxialDistance_after_right_swap_of_succ
            T a b hsucc hrow_b hcol_b
      have ha := adjacentAxialDistance_sameRow T a hrow_a
      omega
    let y : ℝ := (adjacentAxialDistance T b : ℝ)
    let z : ℝ := ((1 : Int) + adjacentAxialDistance T b : Int)
    have hy : y ≠ 0 := by
      have hy_int := adjacentAxialDistance_ne_zero_of_swappable
        T b hrow_b hcol_b
      have hy_real : ((adjacentAxialDistance T b : ℝ) ≠ 0) := by
        exact_mod_cast hy_int
      simpa [y] using hy_real
    have hz0 : z ≠ 0 := by
      have hz_int := adjacentAxialDistance_ne_zero_of_swappable
        Tb a hrow_a_after_b hcol_a_after_b
      have hz_real : ((adjacentAxialDistance Tb a : ℝ) ≠ 0) := by
        exact_mod_cast hz_int
      have hz_eq : ((adjacentAxialDistance Tb a : ℝ)) = z := by
        rw [hdist_after]
      rwa [hz_eq] at hz_real
    have hsum : z = 1 + y := by
      simp [z, y]
    have hzsum : (1 : ℝ) + y ≠ 0 := by
      simpa [← hsum] using hz0
    have hdz : dz = z⁻¹ := by
      change youngAdjacentDiagCoeff Tb a = z⁻¹
      rw [youngAdjacentDiagCoeff, hdist_after]
    have hdb : db = y⁻¹ := by
      change youngAdjacentDiagCoeff T b = y⁻¹
      simp [y, youngAdjacentDiagCoeff]
    have hT_coeff : db ^ 2 + ob ^ 2 * dz = db := by
      have hob_sq : ob ^ 2 = 1 - db ^ 2 := by nlinarith
      rw [hdb, hdz, hob_sq]
      rw [hdb, hsum]
      field_simp [hy, hzsum]
      ring
    have hTb_coeff : db * ob - ob * dz * db = ob * dz := by
      rw [hdb, hdz]
      rw [hsum]
      field_simp [hy, hzsum]
      ring
    rw [hleft, hright]
    funext S
    rw [hT_coeff, hTb_coeff]
    ring

theorem youngAdjacentOperator_braid_basis_left_sameCol_right_swappable_of_succ
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hsucc : (b : Nat) = (a : Nat) + 1)
    (hcol_a : adjacentSameCol T a)
    (hrow_b : ¬ adjacentSameRow T b)
    (hcol_b : ¬ adjacentSameCol T b) :
    youngAdjacentOperator a
        (youngAdjacentOperator b
          (youngAdjacentOperator a (tableauBasisVec T))) =
      youngAdjacentOperator b
        (youngAdjacentOperator a
          (youngAdjacentOperator b (tableauBasisVec T))) := by
  let Tb := adjacentSwapTableau T b hrow_b hcol_b
  let db := youngAdjacentDiagCoeff T b
  let ob := youngAdjacentOffCoeff T b
  have hcol_a_after_b : ¬ adjacentSameCol Tb a := by
    simpa [Tb] using
      not_adjacentSameCol_after_right_swap_of_left_sameCol_of_succ
        T a b hsucc hcol_a hrow_b hcol_b
  have hrow_b_after_b : ¬ adjacentSameRow Tb b := by
    simpa [Tb] using not_adjacentSameRow_swap T b hrow_b hcol_b
  have hcol_b_after_b : ¬ adjacentSameCol Tb b := by
    simpa [Tb] using not_adjacentSameCol_swap T b hrow_b hcol_b
  have hinv_b :
      adjacentSwapTableau Tb b hrow_b_after_b hcol_b_after_b = T := by
    simpa [Tb] using
      adjacentSwapTableau_involutive T b hrow_b hcol_b
        hrow_b_after_b hcol_b_after_b
  have hdiag_Tb_b : youngAdjacentDiagCoeff Tb b = -db := by
    simpa [Tb, db] using youngAdjacentDiagCoeff_swap T b hrow_b hcol_b
  have hoff_Tb_b : youngAdjacentOffCoeff Tb b = ob := by
    simpa [Tb, ob] using youngAdjacentOffCoeff_swap T b hrow_b hcol_b
  have hcoeff_b : db ^ 2 + ob ^ 2 = 1 := by
    simpa [db, ob] using
      youngAdjacentCoeff_sq_sum_of_swappable T b hrow_b hcol_b
  by_cases hrow_a_after_b : adjacentSameRow Tb a
  · have hdist_b : adjacentAxialDistance T b = 2 := by
      have hafter :
          adjacentAxialDistance Tb a =
            adjacentAxialDistance T a + adjacentAxialDistance T b := by
        simpa [Tb] using
          adjacentAxialDistance_after_right_swap_of_succ
            T a b hsucc hrow_b hcol_b
      have ha := adjacentAxialDistance_sameCol T a hcol_a
      have hafter_row := adjacentAxialDistance_sameRow Tb a hrow_a_after_b
      omega
    have hdb : db = (1 / 2 : ℝ) := by
      change youngAdjacentDiagCoeff T b = (1 / 2 : ℝ)
      rw [youngAdjacentDiagCoeff, hdist_b]
      norm_num
    have hT_coeff : -db ^ 2 + ob ^ 2 = db := by
      nlinarith
    have hTb_coeff : -(db * ob) - ob * db = -ob := by
      nlinarith
    have hleft :
        youngAdjacentOperator a
            (youngAdjacentOperator b
              (youngAdjacentOperator a (tableauBasisVec T))) =
          fun S => db * tableauBasisVec T S - ob * tableauBasisVec Tb S := by
      rw [youngAdjacentOperator_basis_sameCol T a hcol_a,
        youngAdjacentOperator_neg,
        youngAdjacentOperator_basis_swappable_eq T b hrow_b hcol_b,
        youngAdjacentOperator_neg,
        youngAdjacentOperator_add, youngAdjacentOperator_smul,
        youngAdjacentOperator_smul,
        youngAdjacentOperator_basis_sameCol T a hcol_a,
        youngAdjacentOperator_basis_sameRow Tb a hrow_a_after_b]
      funext S
      ring
    have hright :
        youngAdjacentOperator b
            (youngAdjacentOperator a
              (youngAdjacentOperator b (tableauBasisVec T))) =
          fun S =>
            (-db ^ 2 + ob ^ 2) * tableauBasisVec T S +
              (-(db * ob) - ob * db) * tableauBasisVec Tb S := by
      rw [youngAdjacentOperator_basis_swappable_eq T b hrow_b hcol_b,
        youngAdjacentOperator_add, youngAdjacentOperator_smul,
        youngAdjacentOperator_smul,
        youngAdjacentOperator_basis_sameCol T a hcol_a,
        youngAdjacentOperator_basis_sameRow Tb a hrow_a_after_b,
        youngAdjacentOperator_add, youngAdjacentOperator_smul,
        youngAdjacentOperator_smul, youngAdjacentOperator_neg,
        youngAdjacentOperator_basis_swappable_eq T b hrow_b hcol_b,
        youngAdjacentOperator_basis_swappable_eq Tb b hrow_b_after_b
          hcol_b_after_b]
      funext S
      rw [hdiag_Tb_b, hoff_Tb_b, hinv_b]
      ring
    rw [hleft, hright]
    funext S
    rw [hT_coeff, hTb_coeff]
    ring
  · let Tba := adjacentSwapTableau Tb a hrow_a_after_b hcol_a_after_b
    let dz := youngAdjacentDiagCoeff Tb a
    let oz := youngAdjacentOffCoeff Tb a
    have hdist_Tba_b :
        adjacentAxialDistance Tba b = -1 := by
      have hdist0 :
          adjacentAxialDistance Tba b = adjacentAxialDistance T a := by
        simpa [Tb, Tba] using
          adjacentAxialDistance_after_right_left_swap_of_succ
            T a b hsucc hrow_b hcol_b hrow_a_after_b hcol_a_after_b
      have ha := adjacentAxialDistance_sameCol T a hcol_a
      omega
    have hdiag_Tba_b : youngAdjacentDiagCoeff Tba b = -1 := by
      rw [youngAdjacentDiagCoeff, hdist_Tba_b]
      norm_num
    have hcol_b_after_a_after_b : adjacentSameCol Tba b := by
      exact adjacentSameCol_of_axialDistance_eq_neg_one
        Tba b hdist_Tba_b
    have hleft :
        youngAdjacentOperator a
            (youngAdjacentOperator b
              (youngAdjacentOperator a (tableauBasisVec T))) =
          fun S =>
            db * tableauBasisVec T S -
              ob * (dz * tableauBasisVec Tb S +
                oz * tableauBasisVec Tba S) := by
      rw [youngAdjacentOperator_basis_sameCol T a hcol_a,
        youngAdjacentOperator_neg,
        youngAdjacentOperator_basis_swappable_eq T b hrow_b hcol_b,
        youngAdjacentOperator_neg,
        youngAdjacentOperator_add, youngAdjacentOperator_smul,
        youngAdjacentOperator_smul,
        youngAdjacentOperator_basis_sameCol T a hcol_a,
        youngAdjacentOperator_basis_swappable_eq Tb a hrow_a_after_b
          hcol_a_after_b]
      funext S
      ring
    have hright :
        youngAdjacentOperator b
            (youngAdjacentOperator a
              (youngAdjacentOperator b (tableauBasisVec T))) =
          fun S =>
            (-db ^ 2 + ob ^ 2 * dz) * tableauBasisVec T S +
              (-(db * ob) - ob * dz * db) * tableauBasisVec Tb S -
              ob * oz * tableauBasisVec Tba S := by
      rw [youngAdjacentOperator_basis_swappable_eq T b hrow_b hcol_b,
        youngAdjacentOperator_add, youngAdjacentOperator_smul,
        youngAdjacentOperator_smul,
        youngAdjacentOperator_basis_sameCol T a hcol_a,
        youngAdjacentOperator_basis_swappable_eq Tb a hrow_a_after_b
          hcol_a_after_b,
        youngAdjacentOperator_add, youngAdjacentOperator_smul,
        youngAdjacentOperator_smul, youngAdjacentOperator_neg,
        youngAdjacentOperator_basis_swappable_eq T b hrow_b hcol_b,
        youngAdjacentOperator_add, youngAdjacentOperator_smul,
        youngAdjacentOperator_smul,
        youngAdjacentOperator_basis_swappable_eq Tb b hrow_b_after_b
          hcol_b_after_b,
        youngAdjacentOperator_basis_sameCol Tba b hcol_b_after_a_after_b]
      funext S
      rw [hdiag_Tb_b, hoff_Tb_b, hinv_b]
      ring
    have hdist_after :
        adjacentAxialDistance Tb a =
          -1 + adjacentAxialDistance T b := by
      have hafter :
          adjacentAxialDistance Tb a =
            adjacentAxialDistance T a + adjacentAxialDistance T b := by
        simpa [Tb] using
          adjacentAxialDistance_after_right_swap_of_succ
            T a b hsucc hrow_b hcol_b
      have ha := adjacentAxialDistance_sameCol T a hcol_a
      omega
    let y : ℝ := (adjacentAxialDistance T b : ℝ)
    let z : ℝ := ((-1 : Int) + adjacentAxialDistance T b : Int)
    have hy : y ≠ 0 := by
      have hy_int := adjacentAxialDistance_ne_zero_of_swappable
        T b hrow_b hcol_b
      have hy_real : ((adjacentAxialDistance T b : ℝ) ≠ 0) := by
        exact_mod_cast hy_int
      simpa [y] using hy_real
    have hz0 : z ≠ 0 := by
      have hz_int := adjacentAxialDistance_ne_zero_of_swappable
        Tb a hrow_a_after_b hcol_a_after_b
      have hz_real : ((adjacentAxialDistance Tb a : ℝ) ≠ 0) := by
        exact_mod_cast hz_int
      have hz_eq : ((adjacentAxialDistance Tb a : ℝ)) = z := by
        rw [hdist_after]
      rwa [hz_eq] at hz_real
    have hsum : z = -1 + y := by
      simp [z, y]
    have hzsum : (-1 : ℝ) + y ≠ 0 := by
      simpa [← hsum] using hz0
    have hdz : dz = z⁻¹ := by
      change youngAdjacentDiagCoeff Tb a = z⁻¹
      rw [youngAdjacentDiagCoeff, hdist_after]
    have hdb : db = y⁻¹ := by
      change youngAdjacentDiagCoeff T b = y⁻¹
      simp [y, youngAdjacentDiagCoeff]
    have hT_coeff : -db ^ 2 + ob ^ 2 * dz = db := by
      have hob_sq : ob ^ 2 = 1 - db ^ 2 := by nlinarith
      rw [hdb, hdz, hob_sq]
      rw [hdb, hsum]
      field_simp [hy, hzsum]
      ring
    have hTb_coeff : -(db * ob) - ob * dz * db = -(ob * dz) := by
      rw [hdb, hdz]
      rw [hsum]
      field_simp [hy, hzsum]
      ring
    rw [hleft, hright]
    funext S
    rw [hT_coeff, hTb_coeff]
    ring

theorem youngAdjacentOperator_braid_basis_left_swappable_right_sameRow_of_succ
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hsucc : (b : Nat) = (a : Nat) + 1)
    (hrow_a : ¬ adjacentSameRow T a)
    (hcol_a : ¬ adjacentSameCol T a)
    (hrow_b : adjacentSameRow T b) :
    youngAdjacentOperator a
        (youngAdjacentOperator b
          (youngAdjacentOperator a (tableauBasisVec T))) =
      youngAdjacentOperator b
        (youngAdjacentOperator a
          (youngAdjacentOperator b (tableauBasisVec T))) := by
  let Ta := adjacentSwapTableau T a hrow_a hcol_a
  let da := youngAdjacentDiagCoeff T a
  let oa := youngAdjacentOffCoeff T a
  have hrow_b_after_a : ¬ adjacentSameRow Ta b := by
    simpa [Ta] using
      not_adjacentSameRow_after_left_swap_of_right_sameRow_of_succ
        T a b hsucc hrow_b hrow_a hcol_a
  have hrow_a_after_a : ¬ adjacentSameRow Ta a := by
    simpa [Ta] using not_adjacentSameRow_swap T a hrow_a hcol_a
  have hcol_a_after_a : ¬ adjacentSameCol Ta a := by
    simpa [Ta] using not_adjacentSameCol_swap T a hrow_a hcol_a
  have hinv_a :
      adjacentSwapTableau Ta a hrow_a_after_a hcol_a_after_a = T := by
    simpa [Ta] using
      adjacentSwapTableau_involutive T a hrow_a hcol_a
        hrow_a_after_a hcol_a_after_a
  have hdiag_Ta_a : youngAdjacentDiagCoeff Ta a = -da := by
    simpa [Ta, da] using youngAdjacentDiagCoeff_swap T a hrow_a hcol_a
  have hoff_Ta_a : youngAdjacentOffCoeff Ta a = oa := by
    simpa [Ta, oa] using youngAdjacentOffCoeff_swap T a hrow_a hcol_a
  have hcoeff_a : da ^ 2 + oa ^ 2 = 1 := by
    simpa [da, oa] using
      youngAdjacentCoeff_sq_sum_of_swappable T a hrow_a hcol_a
  by_cases hcol_b_after_a : adjacentSameCol Ta b
  · have hdist_a : adjacentAxialDistance T a = -2 := by
      have hafter :
          adjacentAxialDistance Ta b =
            adjacentAxialDistance T a + adjacentAxialDistance T b := by
        simpa [Ta] using
          adjacentAxialDistance_after_left_swap_of_succ
            T a b hsucc hrow_a hcol_a
      have hb := adjacentAxialDistance_sameRow T b hrow_b
      have hafter_col := adjacentAxialDistance_sameCol Ta b hcol_b_after_a
      omega
    have hda : da = -(1 / 2 : ℝ) := by
      change youngAdjacentDiagCoeff T a = -(1 / 2 : ℝ)
      rw [youngAdjacentDiagCoeff, hdist_a]
      norm_num
    have hT_coeff : da ^ 2 - oa ^ 2 = da := by
      nlinarith
    have hTa_coeff : da * oa + oa * da = -oa := by
      nlinarith
    have hleft :
        youngAdjacentOperator a
            (youngAdjacentOperator b
              (youngAdjacentOperator a (tableauBasisVec T))) =
          fun S =>
            (da ^ 2 - oa ^ 2) * tableauBasisVec T S +
              (da * oa + oa * da) * tableauBasisVec Ta S := by
      rw [youngAdjacentOperator_basis_swappable_eq T a hrow_a hcol_a,
        youngAdjacentOperator_add, youngAdjacentOperator_smul,
        youngAdjacentOperator_smul,
        youngAdjacentOperator_basis_sameRow T b hrow_b,
        youngAdjacentOperator_basis_sameCol Ta b hcol_b_after_a,
        youngAdjacentOperator_add, youngAdjacentOperator_smul,
        youngAdjacentOperator_smul,
        youngAdjacentOperator_basis_swappable_eq T a hrow_a hcol_a,
        youngAdjacentOperator_neg,
        youngAdjacentOperator_basis_swappable_eq Ta a hrow_a_after_a
          hcol_a_after_a]
      funext S
      rw [hdiag_Ta_a, hoff_Ta_a, hinv_a]
      ring
    have hright :
        youngAdjacentOperator b
            (youngAdjacentOperator a
              (youngAdjacentOperator b (tableauBasisVec T))) =
          fun S => da * tableauBasisVec T S - oa * tableauBasisVec Ta S := by
      rw [youngAdjacentOperator_basis_sameRow T b hrow_b,
        youngAdjacentOperator_basis_swappable_eq T a hrow_a hcol_a,
        youngAdjacentOperator_add, youngAdjacentOperator_smul,
        youngAdjacentOperator_smul,
        youngAdjacentOperator_basis_sameRow T b hrow_b,
        youngAdjacentOperator_basis_sameCol Ta b hcol_b_after_a]
      funext S
      ring
    rw [hleft, hright]
    funext S
    rw [hT_coeff, hTa_coeff]
    ring
  · let Tab := adjacentSwapTableau Ta b hrow_b_after_a hcol_b_after_a
    let dz := youngAdjacentDiagCoeff Ta b
    let oz := youngAdjacentOffCoeff Ta b
    have hdist_Tab_a :
        adjacentAxialDistance Tab a = 1 := by
      have hdist0 :
          adjacentAxialDistance Tab a = adjacentAxialDistance T b := by
        simpa [Ta, Tab] using
          adjacentAxialDistance_after_left_right_swap_of_succ
            T a b hsucc hrow_a hcol_a hrow_b_after_a hcol_b_after_a
      have hb := adjacentAxialDistance_sameRow T b hrow_b
      omega
    have hrow_a_after_b_after_a : adjacentSameRow Tab a := by
      exact adjacentSameRow_of_axialDistance_eq_one Tab a hdist_Tab_a
    have hleft :
        youngAdjacentOperator a
            (youngAdjacentOperator b
              (youngAdjacentOperator a (tableauBasisVec T))) =
          fun S =>
            (da ^ 2 + oa ^ 2 * dz) * tableauBasisVec T S +
              (da * oa - oa * dz * da) * tableauBasisVec Ta S +
              oa * oz * tableauBasisVec Tab S := by
      rw [youngAdjacentOperator_basis_swappable_eq T a hrow_a hcol_a,
        youngAdjacentOperator_add, youngAdjacentOperator_smul,
        youngAdjacentOperator_smul,
        youngAdjacentOperator_basis_sameRow T b hrow_b,
        youngAdjacentOperator_basis_swappable_eq Ta b hrow_b_after_a
          hcol_b_after_a,
        youngAdjacentOperator_add, youngAdjacentOperator_smul,
        youngAdjacentOperator_smul,
        youngAdjacentOperator_add, youngAdjacentOperator_smul,
        youngAdjacentOperator_smul,
        youngAdjacentOperator_basis_swappable_eq T a hrow_a hcol_a,
        youngAdjacentOperator_basis_swappable_eq Ta a hrow_a_after_a
          hcol_a_after_a,
        youngAdjacentOperator_basis_sameRow Tab a hrow_a_after_b_after_a]
      funext S
      rw [hdiag_Ta_a, hoff_Ta_a, hinv_a]
      ring
    have hright :
        youngAdjacentOperator b
            (youngAdjacentOperator a
              (youngAdjacentOperator b (tableauBasisVec T))) =
          fun S =>
            da * tableauBasisVec T S +
              oa * (dz * tableauBasisVec Ta S +
                oz * tableauBasisVec Tab S) := by
      rw [youngAdjacentOperator_basis_sameRow T b hrow_b,
        youngAdjacentOperator_basis_swappable_eq T a hrow_a hcol_a,
        youngAdjacentOperator_add, youngAdjacentOperator_smul,
        youngAdjacentOperator_smul,
        youngAdjacentOperator_basis_sameRow T b hrow_b,
        youngAdjacentOperator_basis_swappable_eq Ta b hrow_b_after_a
          hcol_b_after_a]
    have hdist_after :
        adjacentAxialDistance Ta b =
          adjacentAxialDistance T a + 1 := by
      have hafter :
          adjacentAxialDistance Ta b =
            adjacentAxialDistance T a + adjacentAxialDistance T b := by
        simpa [Ta] using
          adjacentAxialDistance_after_left_swap_of_succ
            T a b hsucc hrow_a hcol_a
      have hb := adjacentAxialDistance_sameRow T b hrow_b
      omega
    let x : ℝ := (adjacentAxialDistance T a : ℝ)
    let z : ℝ := (adjacentAxialDistance T a + (1 : Int) : ℝ)
    have hx : x ≠ 0 := by
      have hx_int := adjacentAxialDistance_ne_zero_of_swappable
        T a hrow_a hcol_a
      have hx_real : ((adjacentAxialDistance T a : ℝ) ≠ 0) := by
        exact_mod_cast hx_int
      simpa [x] using hx_real
    have hz0 : z ≠ 0 := by
      have hz_int := adjacentAxialDistance_ne_zero_of_swappable
        Ta b hrow_b_after_a hcol_b_after_a
      have hz_real : ((adjacentAxialDistance Ta b : ℝ) ≠ 0) := by
        exact_mod_cast hz_int
      have hz_eq : ((adjacentAxialDistance Ta b : ℝ)) = z := by
        rw [hdist_after]
        simp [z]
      rwa [hz_eq] at hz_real
    have hsum : z = x + 1 := by
      simp [z, x]
    have hzsum : x + 1 ≠ 0 := by
      simpa [← hsum] using hz0
    have hdz : dz = z⁻¹ := by
      change youngAdjacentDiagCoeff Ta b = z⁻¹
      rw [youngAdjacentDiagCoeff, hdist_after]
      simp [z]
    have hda : da = x⁻¹ := by
      change youngAdjacentDiagCoeff T a = x⁻¹
      simp [x, youngAdjacentDiagCoeff]
    have hT_coeff : da ^ 2 + oa ^ 2 * dz = da := by
      have hoa_sq : oa ^ 2 = 1 - da ^ 2 := by nlinarith
      rw [hda, hdz, hoa_sq]
      rw [hda, hsum]
      field_simp [hx, hzsum]
      ring
    have hTa_coeff : da * oa - oa * dz * da = oa * dz := by
      rw [hda, hdz]
      rw [hsum]
      field_simp [hx, hzsum]
      ring
    rw [hleft, hright]
    funext S
    rw [hT_coeff, hTa_coeff]
    ring

theorem youngAdjacentOperator_braid_basis_left_swappable_right_sameCol_of_succ
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hsucc : (b : Nat) = (a : Nat) + 1)
    (hrow_a : ¬ adjacentSameRow T a)
    (hcol_a : ¬ adjacentSameCol T a)
    (hcol_b : adjacentSameCol T b) :
    youngAdjacentOperator a
        (youngAdjacentOperator b
          (youngAdjacentOperator a (tableauBasisVec T))) =
      youngAdjacentOperator b
        (youngAdjacentOperator a
          (youngAdjacentOperator b (tableauBasisVec T))) := by
  let Ta := adjacentSwapTableau T a hrow_a hcol_a
  let da := youngAdjacentDiagCoeff T a
  let oa := youngAdjacentOffCoeff T a
  have hcol_b_after_a : ¬ adjacentSameCol Ta b := by
    simpa [Ta] using
      not_adjacentSameCol_after_left_swap_of_right_sameCol_of_succ
        T a b hsucc hcol_b hrow_a hcol_a
  have hrow_a_after_a : ¬ adjacentSameRow Ta a := by
    simpa [Ta] using not_adjacentSameRow_swap T a hrow_a hcol_a
  have hcol_a_after_a : ¬ adjacentSameCol Ta a := by
    simpa [Ta] using not_adjacentSameCol_swap T a hrow_a hcol_a
  have hinv_a :
      adjacentSwapTableau Ta a hrow_a_after_a hcol_a_after_a = T := by
    simpa [Ta] using
      adjacentSwapTableau_involutive T a hrow_a hcol_a
        hrow_a_after_a hcol_a_after_a
  have hdiag_Ta_a : youngAdjacentDiagCoeff Ta a = -da := by
    simpa [Ta, da] using youngAdjacentDiagCoeff_swap T a hrow_a hcol_a
  have hoff_Ta_a : youngAdjacentOffCoeff Ta a = oa := by
    simpa [Ta, oa] using youngAdjacentOffCoeff_swap T a hrow_a hcol_a
  have hcoeff_a : da ^ 2 + oa ^ 2 = 1 := by
    simpa [da, oa] using
      youngAdjacentCoeff_sq_sum_of_swappable T a hrow_a hcol_a
  by_cases hrow_b_after_a : adjacentSameRow Ta b
  · have hdist_a : adjacentAxialDistance T a = 2 := by
      have hafter :
          adjacentAxialDistance Ta b =
            adjacentAxialDistance T a + adjacentAxialDistance T b := by
        simpa [Ta] using
          adjacentAxialDistance_after_left_swap_of_succ
            T a b hsucc hrow_a hcol_a
      have hb := adjacentAxialDistance_sameCol T b hcol_b
      have hafter_row := adjacentAxialDistance_sameRow Ta b hrow_b_after_a
      omega
    have hda : da = (1 / 2 : ℝ) := by
      change youngAdjacentDiagCoeff T a = (1 / 2 : ℝ)
      rw [youngAdjacentDiagCoeff, hdist_a]
      norm_num
    have hT_coeff : -da ^ 2 + oa ^ 2 = da := by
      nlinarith
    have hTa_coeff : -(da * oa) - oa * da = -oa := by
      nlinarith
    have hleft :
        youngAdjacentOperator a
            (youngAdjacentOperator b
              (youngAdjacentOperator a (tableauBasisVec T))) =
          fun S =>
            (-da ^ 2 + oa ^ 2) * tableauBasisVec T S +
              (-(da * oa) - oa * da) * tableauBasisVec Ta S := by
      rw [youngAdjacentOperator_basis_swappable_eq T a hrow_a hcol_a,
        youngAdjacentOperator_add, youngAdjacentOperator_smul,
        youngAdjacentOperator_smul,
        youngAdjacentOperator_basis_sameCol T b hcol_b,
        youngAdjacentOperator_basis_sameRow Ta b hrow_b_after_a,
        youngAdjacentOperator_add, youngAdjacentOperator_smul,
        youngAdjacentOperator_smul, youngAdjacentOperator_neg,
        youngAdjacentOperator_basis_swappable_eq T a hrow_a hcol_a,
        youngAdjacentOperator_basis_swappable_eq Ta a hrow_a_after_a
          hcol_a_after_a]
      funext S
      rw [hdiag_Ta_a, hoff_Ta_a, hinv_a]
      ring
    have hright :
        youngAdjacentOperator b
            (youngAdjacentOperator a
              (youngAdjacentOperator b (tableauBasisVec T))) =
          fun S => da * tableauBasisVec T S - oa * tableauBasisVec Ta S := by
      rw [youngAdjacentOperator_basis_sameCol T b hcol_b,
        youngAdjacentOperator_neg,
        youngAdjacentOperator_basis_swappable_eq T a hrow_a hcol_a,
        youngAdjacentOperator_neg,
        youngAdjacentOperator_add, youngAdjacentOperator_smul,
        youngAdjacentOperator_smul,
        youngAdjacentOperator_basis_sameCol T b hcol_b,
        youngAdjacentOperator_basis_sameRow Ta b hrow_b_after_a]
      funext S
      ring
    rw [hleft, hright]
    funext S
    rw [hT_coeff, hTa_coeff]
    ring
  · let Tab := adjacentSwapTableau Ta b hrow_b_after_a hcol_b_after_a
    let dz := youngAdjacentDiagCoeff Ta b
    let oz := youngAdjacentOffCoeff Ta b
    have hdist_Tab_a :
        adjacentAxialDistance Tab a = -1 := by
      have hdist0 :
          adjacentAxialDistance Tab a = adjacentAxialDistance T b := by
        simpa [Ta, Tab] using
          adjacentAxialDistance_after_left_right_swap_of_succ
            T a b hsucc hrow_a hcol_a hrow_b_after_a hcol_b_after_a
      have hb := adjacentAxialDistance_sameCol T b hcol_b
      omega
    have hcol_a_after_b_after_a : adjacentSameCol Tab a := by
      exact adjacentSameCol_of_axialDistance_eq_neg_one Tab a hdist_Tab_a
    have hleft :
        youngAdjacentOperator a
            (youngAdjacentOperator b
              (youngAdjacentOperator a (tableauBasisVec T))) =
          fun S =>
            (-da ^ 2 + oa ^ 2 * dz) * tableauBasisVec T S +
              (-(da * oa) - oa * dz * da) * tableauBasisVec Ta S -
              oa * oz * tableauBasisVec Tab S := by
      rw [youngAdjacentOperator_basis_swappable_eq T a hrow_a hcol_a,
        youngAdjacentOperator_add, youngAdjacentOperator_smul,
        youngAdjacentOperator_smul,
        youngAdjacentOperator_basis_sameCol T b hcol_b,
        youngAdjacentOperator_basis_swappable_eq Ta b hrow_b_after_a
          hcol_b_after_a,
        youngAdjacentOperator_add, youngAdjacentOperator_smul,
        youngAdjacentOperator_smul, youngAdjacentOperator_neg,
        youngAdjacentOperator_add, youngAdjacentOperator_smul,
        youngAdjacentOperator_smul,
        youngAdjacentOperator_basis_swappable_eq T a hrow_a hcol_a,
        youngAdjacentOperator_basis_swappable_eq Ta a hrow_a_after_a
          hcol_a_after_a,
        youngAdjacentOperator_basis_sameCol Tab a hcol_a_after_b_after_a]
      funext S
      rw [hdiag_Ta_a, hoff_Ta_a, hinv_a]
      ring
    have hright :
        youngAdjacentOperator b
            (youngAdjacentOperator a
              (youngAdjacentOperator b (tableauBasisVec T))) =
          fun S =>
            da * tableauBasisVec T S -
              oa * (dz * tableauBasisVec Ta S +
                oz * tableauBasisVec Tab S) := by
      rw [youngAdjacentOperator_basis_sameCol T b hcol_b,
        youngAdjacentOperator_neg,
        youngAdjacentOperator_basis_swappable_eq T a hrow_a hcol_a,
        youngAdjacentOperator_neg,
        youngAdjacentOperator_add, youngAdjacentOperator_smul,
        youngAdjacentOperator_smul,
        youngAdjacentOperator_basis_sameCol T b hcol_b,
        youngAdjacentOperator_basis_swappable_eq Ta b hrow_b_after_a
          hcol_b_after_a]
      funext S
      ring
    have hdist_after :
        adjacentAxialDistance Ta b =
          adjacentAxialDistance T a - 1 := by
      have hafter :
          adjacentAxialDistance Ta b =
            adjacentAxialDistance T a + adjacentAxialDistance T b := by
        simpa [Ta] using
          adjacentAxialDistance_after_left_swap_of_succ
            T a b hsucc hrow_a hcol_a
      have hb := adjacentAxialDistance_sameCol T b hcol_b
      omega
    let x : ℝ := (adjacentAxialDistance T a : ℝ)
    let z : ℝ := (adjacentAxialDistance T a - (1 : Int) : ℝ)
    have hx : x ≠ 0 := by
      have hx_int := adjacentAxialDistance_ne_zero_of_swappable
        T a hrow_a hcol_a
      have hx_real : ((adjacentAxialDistance T a : ℝ) ≠ 0) := by
        exact_mod_cast hx_int
      simpa [x] using hx_real
    have hz0 : z ≠ 0 := by
      have hz_int := adjacentAxialDistance_ne_zero_of_swappable
        Ta b hrow_b_after_a hcol_b_after_a
      have hz_real : ((adjacentAxialDistance Ta b : ℝ) ≠ 0) := by
        exact_mod_cast hz_int
      have hz_eq : ((adjacentAxialDistance Ta b : ℝ)) = z := by
        rw [hdist_after]
        simp [z]
      rwa [hz_eq] at hz_real
    have hsum : z = x - 1 := by
      simp [z, x]
    have hzsum : x - 1 ≠ 0 := by
      simpa [← hsum] using hz0
    have hdz : dz = z⁻¹ := by
      change youngAdjacentDiagCoeff Ta b = z⁻¹
      rw [youngAdjacentDiagCoeff, hdist_after]
      simp [z]
    have hda : da = x⁻¹ := by
      change youngAdjacentDiagCoeff T a = x⁻¹
      simp [x, youngAdjacentDiagCoeff]
    have hT_coeff : -da ^ 2 + oa ^ 2 * dz = da := by
      have hoa_sq : oa ^ 2 = 1 - da ^ 2 := by nlinarith
      rw [hda, hdz, hoa_sq]
      rw [hda, hsum]
      field_simp [hx, hzsum]
      ring
    have hTa_coeff : -(da * oa) - oa * dz * da = -(oa * dz) := by
      rw [hda, hdz]
      rw [hsum]
      field_simp [hx, hzsum]
      ring
    rw [hleft, hright]
    funext S
    rw [hT_coeff, hTa_coeff]
    ring

theorem youngAdjacentOperator_braid_basis_swappable_middle_sameRow_of_succ
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hsucc : (b : Nat) = (a : Nat) + 1)
    (hrow_a : ¬ adjacentSameRow T a)
    (hcol_a : ¬ adjacentSameCol T a)
    (hrow_b : ¬ adjacentSameRow T b)
    (hcol_b : ¬ adjacentSameCol T b)
    (hrow_b_after_a :
      adjacentSameRow (adjacentSwapTableau T a hrow_a hcol_a) b) :
    youngAdjacentOperator a
        (youngAdjacentOperator b
          (youngAdjacentOperator a (tableauBasisVec T))) =
      youngAdjacentOperator b
        (youngAdjacentOperator a
          (youngAdjacentOperator b (tableauBasisVec T))) := by
  let Ta := adjacentSwapTableau T a hrow_a hcol_a
  let Tb := adjacentSwapTableau T b hrow_b hcol_b
  let da := youngAdjacentDiagCoeff T a
  let db := youngAdjacentDiagCoeff T b
  let oa := youngAdjacentOffCoeff T a
  let ob := youngAdjacentOffCoeff T b
  have hsum_int :
      adjacentAxialDistance T a + adjacentAxialDistance T b = 1 := by
    have hafter :
        adjacentAxialDistance Ta b =
          adjacentAxialDistance T a + adjacentAxialDistance T b := by
      simpa [Ta] using
        adjacentAxialDistance_after_left_swap_of_succ
          T a b hsucc hrow_a hcol_a
    have hsame := adjacentAxialDistance_sameRow Ta b hrow_b_after_a
    omega
  have hdist_Tb_a : adjacentAxialDistance Tb a = 1 := by
    have hafter :
        adjacentAxialDistance Tb a =
          adjacentAxialDistance T a + adjacentAxialDistance T b := by
      simpa [Tb] using
        adjacentAxialDistance_after_right_swap_of_succ
          T a b hsucc hrow_b hcol_b
    omega
  have hrow_a_after_b : adjacentSameRow Tb a := by
    exact adjacentSameRow_of_axialDistance_eq_one Tb a hdist_Tb_a
  have hrow_a_after_a : ¬ adjacentSameRow Ta a := by
    simpa [Ta] using not_adjacentSameRow_swap T a hrow_a hcol_a
  have hcol_a_after_a : ¬ adjacentSameCol Ta a := by
    simpa [Ta] using not_adjacentSameCol_swap T a hrow_a hcol_a
  have hrow_b_after_b : ¬ adjacentSameRow Tb b := by
    simpa [Tb] using not_adjacentSameRow_swap T b hrow_b hcol_b
  have hcol_b_after_b : ¬ adjacentSameCol Tb b := by
    simpa [Tb] using not_adjacentSameCol_swap T b hrow_b hcol_b
  have hinv_a :
      adjacentSwapTableau Ta a hrow_a_after_a hcol_a_after_a = T := by
    simpa [Ta] using
      adjacentSwapTableau_involutive T a hrow_a hcol_a
        hrow_a_after_a hcol_a_after_a
  have hinv_b :
      adjacentSwapTableau Tb b hrow_b_after_b hcol_b_after_b = T := by
    simpa [Tb] using
      adjacentSwapTableau_involutive T b hrow_b hcol_b
        hrow_b_after_b hcol_b_after_b
  have hdiag_Ta_a : youngAdjacentDiagCoeff Ta a = -da := by
    simpa [Ta, da] using youngAdjacentDiagCoeff_swap T a hrow_a hcol_a
  have hoff_Ta_a : youngAdjacentOffCoeff Ta a = oa := by
    simpa [Ta, oa] using youngAdjacentOffCoeff_swap T a hrow_a hcol_a
  have hdiag_Tb_b : youngAdjacentDiagCoeff Tb b = -db := by
    simpa [Tb, db] using youngAdjacentDiagCoeff_swap T b hrow_b hcol_b
  have hoff_Tb_b : youngAdjacentOffCoeff Tb b = ob := by
    simpa [Tb, ob] using youngAdjacentOffCoeff_swap T b hrow_b hcol_b
  have hcoeff_a : da ^ 2 + oa ^ 2 = 1 := by
    simpa [da, oa] using
      youngAdjacentCoeff_sq_sum_of_swappable T a hrow_a hcol_a
  have hcoeff_b : db ^ 2 + ob ^ 2 = 1 := by
    simpa [db, ob] using
      youngAdjacentCoeff_sq_sum_of_swappable T b hrow_b hcol_b
  have hleft :
      youngAdjacentOperator a
          (youngAdjacentOperator b
            (youngAdjacentOperator a (tableauBasisVec T))) =
        fun S =>
          (da ^ 2 * db + oa ^ 2) * tableauBasisVec T S +
            (da * db * oa - oa * da) * tableauBasisVec Ta S +
            da * ob * tableauBasisVec Tb S := by
    rw [youngAdjacentOperator_basis_swappable_eq T a hrow_a hcol_a,
      youngAdjacentOperator_add, youngAdjacentOperator_smul,
      youngAdjacentOperator_smul,
      youngAdjacentOperator_basis_swappable_eq T b hrow_b hcol_b,
      youngAdjacentOperator_basis_sameRow Ta b hrow_b_after_a,
      youngAdjacentOperator_add, youngAdjacentOperator_smul,
      youngAdjacentOperator_smul,
      youngAdjacentOperator_add, youngAdjacentOperator_smul,
      youngAdjacentOperator_smul,
      youngAdjacentOperator_basis_swappable_eq T a hrow_a hcol_a,
      youngAdjacentOperator_basis_sameRow Tb a hrow_a_after_b,
      youngAdjacentOperator_basis_swappable_eq Ta a hrow_a_after_a
        hcol_a_after_a]
    funext S
    rw [hdiag_Ta_a, hoff_Ta_a, hinv_a]
    ring
  have hright :
      youngAdjacentOperator b
          (youngAdjacentOperator a
            (youngAdjacentOperator b (tableauBasisVec T))) =
        fun S =>
          (da * db ^ 2 + ob ^ 2) * tableauBasisVec T S +
            db * oa * tableauBasisVec Ta S +
            (da * db * ob - ob * db) * tableauBasisVec Tb S := by
    rw [youngAdjacentOperator_basis_swappable_eq T b hrow_b hcol_b,
      youngAdjacentOperator_add, youngAdjacentOperator_smul,
      youngAdjacentOperator_smul,
      youngAdjacentOperator_basis_swappable_eq T a hrow_a hcol_a,
      youngAdjacentOperator_basis_sameRow Tb a hrow_a_after_b,
      youngAdjacentOperator_add, youngAdjacentOperator_smul,
      youngAdjacentOperator_smul,
      youngAdjacentOperator_add, youngAdjacentOperator_smul,
      youngAdjacentOperator_smul,
      youngAdjacentOperator_basis_swappable_eq T b hrow_b hcol_b,
      youngAdjacentOperator_basis_sameRow Ta b hrow_b_after_a,
      youngAdjacentOperator_basis_swappable_eq Tb b hrow_b_after_b
        hcol_b_after_b]
    funext S
    rw [hdiag_Tb_b, hoff_Tb_b, hinv_b]
    ring
  let x : ℝ := (adjacentAxialDistance T a : ℝ)
  let y : ℝ := (adjacentAxialDistance T b : ℝ)
  have hx : x ≠ 0 := by
    have hx_int := adjacentAxialDistance_ne_zero_of_swappable
      T a hrow_a hcol_a
    have hx_real : ((adjacentAxialDistance T a : ℝ) ≠ 0) := by
      exact_mod_cast hx_int
    simpa [x] using hx_real
  have hy : y ≠ 0 := by
    have hy_int := adjacentAxialDistance_ne_zero_of_swappable
      T b hrow_b hcol_b
    have hy_real : ((adjacentAxialDistance T b : ℝ) ≠ 0) := by
      exact_mod_cast hy_int
    simpa [y] using hy_real
  have hsum : x + y = 1 := by
    have hcast :
        ((adjacentAxialDistance T a +
          adjacentAxialDistance T b : Int) : ℝ) = (1 : ℝ) := by
      exact_mod_cast hsum_int
    simpa [x, y] using hcast
  have hda : da = x⁻¹ := by
    change youngAdjacentDiagCoeff T a = x⁻¹
    simp [x, youngAdjacentDiagCoeff]
  have hdb : db = y⁻¹ := by
    change youngAdjacentDiagCoeff T b = y⁻¹
    simp [y, youngAdjacentDiagCoeff]
  have hT_coeff :
      da ^ 2 * db + oa ^ 2 = da * db ^ 2 + ob ^ 2 := by
    have hoa_sq : oa ^ 2 = 1 - da ^ 2 := by nlinarith
    have hob_sq : ob ^ 2 = 1 - db ^ 2 := by nlinarith
    rw [hoa_sq, hob_sq, hda, hdb]
    field_simp [hx, hy]
    nlinarith [hsum]
  have hTa_coeff : da * db * oa - oa * da = db * oa := by
    rw [hda, hdb]
    field_simp [hx, hy]
    have hx_eq : x = 1 - y := by linarith
    rw [hx_eq]
    ring
  have hTb_coeff : da * ob = da * db * ob - ob * db := by
    rw [hda, hdb]
    field_simp [hx, hy]
    have hy_eq : y = 1 - x := by linarith
    rw [hy_eq]
  rw [hleft, hright]
  funext S
  rw [hT_coeff, hTa_coeff, hTb_coeff]

theorem youngAdjacentOperator_braid_basis_swappable_middle_sameCol_of_succ
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hsucc : (b : Nat) = (a : Nat) + 1)
    (hrow_a : ¬ adjacentSameRow T a)
    (hcol_a : ¬ adjacentSameCol T a)
    (hrow_b : ¬ adjacentSameRow T b)
    (hcol_b : ¬ adjacentSameCol T b)
    (hcol_b_after_a :
      adjacentSameCol (adjacentSwapTableau T a hrow_a hcol_a) b) :
    youngAdjacentOperator a
        (youngAdjacentOperator b
          (youngAdjacentOperator a (tableauBasisVec T))) =
      youngAdjacentOperator b
        (youngAdjacentOperator a
          (youngAdjacentOperator b (tableauBasisVec T))) := by
  let Ta := adjacentSwapTableau T a hrow_a hcol_a
  let Tb := adjacentSwapTableau T b hrow_b hcol_b
  let da := youngAdjacentDiagCoeff T a
  let db := youngAdjacentDiagCoeff T b
  let oa := youngAdjacentOffCoeff T a
  let ob := youngAdjacentOffCoeff T b
  have hsum_int :
      adjacentAxialDistance T a + adjacentAxialDistance T b = -1 := by
    have hafter :
        adjacentAxialDistance Ta b =
          adjacentAxialDistance T a + adjacentAxialDistance T b := by
      simpa [Ta] using
        adjacentAxialDistance_after_left_swap_of_succ
          T a b hsucc hrow_a hcol_a
    have hsame := adjacentAxialDistance_sameCol Ta b hcol_b_after_a
    omega
  have hdist_Tb_a : adjacentAxialDistance Tb a = -1 := by
    have hafter :
        adjacentAxialDistance Tb a =
          adjacentAxialDistance T a + adjacentAxialDistance T b := by
      simpa [Tb] using
        adjacentAxialDistance_after_right_swap_of_succ
          T a b hsucc hrow_b hcol_b
    omega
  have hcol_a_after_b : adjacentSameCol Tb a := by
    exact adjacentSameCol_of_axialDistance_eq_neg_one Tb a hdist_Tb_a
  have hrow_a_after_a : ¬ adjacentSameRow Ta a := by
    simpa [Ta] using not_adjacentSameRow_swap T a hrow_a hcol_a
  have hcol_a_after_a : ¬ adjacentSameCol Ta a := by
    simpa [Ta] using not_adjacentSameCol_swap T a hrow_a hcol_a
  have hrow_b_after_b : ¬ adjacentSameRow Tb b := by
    simpa [Tb] using not_adjacentSameRow_swap T b hrow_b hcol_b
  have hcol_b_after_b : ¬ adjacentSameCol Tb b := by
    simpa [Tb] using not_adjacentSameCol_swap T b hrow_b hcol_b
  have hinv_a :
      adjacentSwapTableau Ta a hrow_a_after_a hcol_a_after_a = T := by
    simpa [Ta] using
      adjacentSwapTableau_involutive T a hrow_a hcol_a
        hrow_a_after_a hcol_a_after_a
  have hinv_b :
      adjacentSwapTableau Tb b hrow_b_after_b hcol_b_after_b = T := by
    simpa [Tb] using
      adjacentSwapTableau_involutive T b hrow_b hcol_b
        hrow_b_after_b hcol_b_after_b
  have hdiag_Ta_a : youngAdjacentDiagCoeff Ta a = -da := by
    simpa [Ta, da] using youngAdjacentDiagCoeff_swap T a hrow_a hcol_a
  have hoff_Ta_a : youngAdjacentOffCoeff Ta a = oa := by
    simpa [Ta, oa] using youngAdjacentOffCoeff_swap T a hrow_a hcol_a
  have hdiag_Tb_b : youngAdjacentDiagCoeff Tb b = -db := by
    simpa [Tb, db] using youngAdjacentDiagCoeff_swap T b hrow_b hcol_b
  have hoff_Tb_b : youngAdjacentOffCoeff Tb b = ob := by
    simpa [Tb, ob] using youngAdjacentOffCoeff_swap T b hrow_b hcol_b
  have hcoeff_a : da ^ 2 + oa ^ 2 = 1 := by
    simpa [da, oa] using
      youngAdjacentCoeff_sq_sum_of_swappable T a hrow_a hcol_a
  have hcoeff_b : db ^ 2 + ob ^ 2 = 1 := by
    simpa [db, ob] using
      youngAdjacentCoeff_sq_sum_of_swappable T b hrow_b hcol_b
  have hleft :
      youngAdjacentOperator a
          (youngAdjacentOperator b
            (youngAdjacentOperator a (tableauBasisVec T))) =
        fun S =>
          (da ^ 2 * db - oa ^ 2) * tableauBasisVec T S +
            (da * db * oa + oa * da) * tableauBasisVec Ta S -
            da * ob * tableauBasisVec Tb S := by
    rw [youngAdjacentOperator_basis_swappable_eq T a hrow_a hcol_a,
      youngAdjacentOperator_add, youngAdjacentOperator_smul,
      youngAdjacentOperator_smul,
      youngAdjacentOperator_basis_swappable_eq T b hrow_b hcol_b,
      youngAdjacentOperator_basis_sameCol Ta b hcol_b_after_a,
      youngAdjacentOperator_add, youngAdjacentOperator_smul,
      youngAdjacentOperator_smul, youngAdjacentOperator_neg,
      youngAdjacentOperator_add, youngAdjacentOperator_smul,
      youngAdjacentOperator_smul,
      youngAdjacentOperator_basis_swappable_eq T a hrow_a hcol_a,
      youngAdjacentOperator_basis_sameCol Tb a hcol_a_after_b,
      youngAdjacentOperator_basis_swappable_eq Ta a hrow_a_after_a
        hcol_a_after_a]
    funext S
    rw [hdiag_Ta_a, hoff_Ta_a, hinv_a]
    ring
  have hright :
      youngAdjacentOperator b
          (youngAdjacentOperator a
            (youngAdjacentOperator b (tableauBasisVec T))) =
        fun S =>
          (da * db ^ 2 - ob ^ 2) * tableauBasisVec T S -
            db * oa * tableauBasisVec Ta S +
            (da * db * ob + ob * db) * tableauBasisVec Tb S := by
    rw [youngAdjacentOperator_basis_swappable_eq T b hrow_b hcol_b,
      youngAdjacentOperator_add, youngAdjacentOperator_smul,
      youngAdjacentOperator_smul,
      youngAdjacentOperator_basis_swappable_eq T a hrow_a hcol_a,
      youngAdjacentOperator_basis_sameCol Tb a hcol_a_after_b,
      youngAdjacentOperator_add, youngAdjacentOperator_smul,
      youngAdjacentOperator_smul, youngAdjacentOperator_neg,
      youngAdjacentOperator_add, youngAdjacentOperator_smul,
      youngAdjacentOperator_smul,
      youngAdjacentOperator_basis_swappable_eq T b hrow_b hcol_b,
      youngAdjacentOperator_basis_sameCol Ta b hcol_b_after_a,
      youngAdjacentOperator_basis_swappable_eq Tb b hrow_b_after_b
        hcol_b_after_b]
    funext S
    rw [hdiag_Tb_b, hoff_Tb_b, hinv_b]
    ring
  let x : ℝ := (adjacentAxialDistance T a : ℝ)
  let y : ℝ := (adjacentAxialDistance T b : ℝ)
  have hx : x ≠ 0 := by
    have hx_int := adjacentAxialDistance_ne_zero_of_swappable
      T a hrow_a hcol_a
    have hx_real : ((adjacentAxialDistance T a : ℝ) ≠ 0) := by
      exact_mod_cast hx_int
    simpa [x] using hx_real
  have hy : y ≠ 0 := by
    have hy_int := adjacentAxialDistance_ne_zero_of_swappable
      T b hrow_b hcol_b
    have hy_real : ((adjacentAxialDistance T b : ℝ) ≠ 0) := by
      exact_mod_cast hy_int
    simpa [y] using hy_real
  have hsum : x + y = -1 := by
    have hcast :
        ((adjacentAxialDistance T a +
          adjacentAxialDistance T b : Int) : ℝ) = (-1 : ℝ) := by
      exact_mod_cast hsum_int
    simpa [x, y] using hcast
  have hda : da = x⁻¹ := by
    change youngAdjacentDiagCoeff T a = x⁻¹
    simp [x, youngAdjacentDiagCoeff]
  have hdb : db = y⁻¹ := by
    change youngAdjacentDiagCoeff T b = y⁻¹
    simp [y, youngAdjacentDiagCoeff]
  have hT_coeff :
      da ^ 2 * db - oa ^ 2 = da * db ^ 2 - ob ^ 2 := by
    have hoa_sq : oa ^ 2 = 1 - da ^ 2 := by nlinarith
    have hob_sq : ob ^ 2 = 1 - db ^ 2 := by nlinarith
    rw [hoa_sq, hob_sq, hda, hdb]
    field_simp [hx, hy]
    nlinarith [hsum]
  have hTa_coeff : da * db * oa + oa * da = -(db * oa) := by
    rw [hda, hdb]
    field_simp [hx, hy]
    have hx_eq : x = -1 - y := by linarith
    rw [hx_eq]
    ring
  have hTb_coeff : -(da * ob) = da * db * ob + ob * db := by
    rw [hda, hdb]
    field_simp [hx, hy]
    have hy_eq : y = -1 - x := by linarith
    rw [hy_eq]
    ring
  rw [hleft, hright]
  funext S
  rw [hT_coeff, hTa_coeff, ← hTb_coeff]
  ring

theorem youngAdjacentOperator_braid_basis_of_succ
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hsucc : (b : Nat) = (a : Nat) + 1) :
    youngAdjacentOperator a
        (youngAdjacentOperator b
          (youngAdjacentOperator a (tableauBasisVec T))) =
      youngAdjacentOperator b
        (youngAdjacentOperator a
          (youngAdjacentOperator b (tableauBasisVec T))) := by
  by_cases hrow_a : adjacentSameRow T a
  · by_cases hrow_b : adjacentSameRow T b
    · exact youngAdjacentOperator_braid_basis_sameRow_sameRow_of_succ
        T a b hsucc hrow_a hrow_b
    · by_cases hcol_b : adjacentSameCol T b
      · exact False.elim
          ((not_adjacentSameRow_and_succ_sameCol T a b hsucc)
            ⟨hrow_a, hcol_b⟩)
      · exact
          youngAdjacentOperator_braid_basis_left_sameRow_right_swappable_of_succ
            T a b hsucc hrow_a hrow_b hcol_b
  · by_cases hcol_a : adjacentSameCol T a
    · by_cases hrow_b : adjacentSameRow T b
      · exact False.elim
          ((not_adjacentSameCol_and_succ_sameRow T a b hsucc)
            ⟨hcol_a, hrow_b⟩)
      · by_cases hcol_b : adjacentSameCol T b
        · exact youngAdjacentOperator_braid_basis_sameCol_sameCol_of_succ
            T a b hsucc hcol_a hcol_b
        · exact
            youngAdjacentOperator_braid_basis_left_sameCol_right_swappable_of_succ
              T a b hsucc hcol_a hrow_b hcol_b
    · by_cases hrow_b : adjacentSameRow T b
      · exact
          youngAdjacentOperator_braid_basis_left_swappable_right_sameRow_of_succ
            T a b hsucc hrow_a hcol_a hrow_b
      · by_cases hcol_b : adjacentSameCol T b
        · exact
            youngAdjacentOperator_braid_basis_left_swappable_right_sameCol_of_succ
              T a b hsucc hrow_a hcol_a hcol_b
        · let Ta := adjacentSwapTableau T a hrow_a hcol_a
          let Tb := adjacentSwapTableau T b hrow_b hcol_b
          by_cases hrow_b_after_a : adjacentSameRow Ta b
          · exact
              youngAdjacentOperator_braid_basis_swappable_middle_sameRow_of_succ
                T a b hsucc hrow_a hcol_a hrow_b hcol_b
                (by simpa [Ta] using hrow_b_after_a)
          · by_cases hcol_b_after_a : adjacentSameCol Ta b
            · exact
                youngAdjacentOperator_braid_basis_swappable_middle_sameCol_of_succ
                  T a b hsucc hrow_a hcol_a hrow_b hcol_b
                  (by simpa [Ta] using hcol_b_after_a)
            · have hrow_a_after_b : ¬ adjacentSameRow Tb a := by
                intro hrow
                have hdist_right :
                    adjacentAxialDistance Tb a =
                      adjacentAxialDistance T a +
                        adjacentAxialDistance T b := by
                  simpa [Tb] using
                    adjacentAxialDistance_after_right_swap_of_succ
                      T a b hsucc hrow_b hcol_b
                have hdist_left :
                    adjacentAxialDistance Ta b =
                      adjacentAxialDistance T a +
                        adjacentAxialDistance T b := by
                  simpa [Ta] using
                    adjacentAxialDistance_after_left_swap_of_succ
                      T a b hsucc hrow_a hcol_a
                have hsame : adjacentAxialDistance Ta b = 1 := by
                  have hr := adjacentAxialDistance_sameRow Tb a hrow
                  omega
                exact hrow_b_after_a
                  (adjacentSameRow_of_axialDistance_eq_one Ta b hsame)
              have hcol_a_after_b : ¬ adjacentSameCol Tb a := by
                intro hcol
                have hdist_right :
                    adjacentAxialDistance Tb a =
                      adjacentAxialDistance T a +
                        adjacentAxialDistance T b := by
                  simpa [Tb] using
                    adjacentAxialDistance_after_right_swap_of_succ
                      T a b hsucc hrow_b hcol_b
                have hdist_left :
                    adjacentAxialDistance Ta b =
                      adjacentAxialDistance T a +
                        adjacentAxialDistance T b := by
                  simpa [Ta] using
                    adjacentAxialDistance_after_left_swap_of_succ
                      T a b hsucc hrow_a hcol_a
                have hsame : adjacentAxialDistance Ta b = -1 := by
                  have hc := adjacentAxialDistance_sameCol Tb a hcol
                  omega
                exact hcol_b_after_a
                  (adjacentSameCol_of_axialDistance_eq_neg_one Ta b hsame)
              let Tab :=
                adjacentSwapTableau Ta b hrow_b_after_a hcol_b_after_a
              let Tba :=
                adjacentSwapTableau Tb a hrow_a_after_b hcol_a_after_b
              have hrow_a_after_b_after_a :
                  ¬ adjacentSameRow Tab a := by
                intro hrow
                have hdist :
                    adjacentAxialDistance Tab a =
                      adjacentAxialDistance T b := by
                  simpa [Ta, Tab] using
                    adjacentAxialDistance_after_left_right_swap_of_succ
                      T a b hsucc hrow_a hcol_a
                      hrow_b_after_a hcol_b_after_a
                have hb_dist := adjacentAxialDistance_sameRow Tab a hrow
                exact hrow_b
                  (adjacentSameRow_of_axialDistance_eq_one T b (by
                    omega))
              have hcol_a_after_b_after_a :
                  ¬ adjacentSameCol Tab a := by
                intro hcol
                have hdist :
                    adjacentAxialDistance Tab a =
                      adjacentAxialDistance T b := by
                  simpa [Ta, Tab] using
                    adjacentAxialDistance_after_left_right_swap_of_succ
                      T a b hsucc hrow_a hcol_a
                      hrow_b_after_a hcol_b_after_a
                have hb_dist := adjacentAxialDistance_sameCol Tab a hcol
                exact hcol_b
                  (adjacentSameCol_of_axialDistance_eq_neg_one T b (by
                    omega))
              have hrow_b_after_a_after_b :
                  ¬ adjacentSameRow Tba b := by
                intro hrow
                have hdist :
                    adjacentAxialDistance Tba b =
                      adjacentAxialDistance T a := by
                  simpa [Tb, Tba] using
                    adjacentAxialDistance_after_right_left_swap_of_succ
                      T a b hsucc hrow_b hcol_b
                      hrow_a_after_b hcol_a_after_b
                have ha_dist := adjacentAxialDistance_sameRow Tba b hrow
                exact hrow_a
                  (adjacentSameRow_of_axialDistance_eq_one T a (by
                    omega))
              have hcol_b_after_a_after_b :
                  ¬ adjacentSameCol Tba b := by
                intro hcol
                have hdist :
                    adjacentAxialDistance Tba b =
                      adjacentAxialDistance T a := by
                  simpa [Tb, Tba] using
                    adjacentAxialDistance_after_right_left_swap_of_succ
                      T a b hsucc hrow_b hcol_b
                      hrow_a_after_b hcol_a_after_b
                have ha_dist := adjacentAxialDistance_sameCol Tba b hcol
                exact hcol_a
                  (adjacentSameCol_of_axialDistance_eq_neg_one T a (by
                    omega))
              exact
                youngAdjacentOperator_braid_basis_swappable_of_succ
                  T a b hsucc hrow_a hcol_a hrow_b hcol_b
                  hrow_b_after_a hcol_b_after_a
                  hrow_a_after_b_after_a hcol_a_after_b_after_a
                  hrow_a_after_b hcol_a_after_b
                  hrow_b_after_a_after_b hcol_b_after_a_after_b

theorem youngAdjacentOperator_braid_smul_basis_of_succ
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hsucc : (b : Nat) = (a : Nat) + 1) (c : ℝ) :
    youngAdjacentOperator a
        (youngAdjacentOperator b
          (youngAdjacentOperator a
            (fun S => c * tableauBasisVec T S))) =
      youngAdjacentOperator b
        (youngAdjacentOperator a
          (youngAdjacentOperator b
            (fun S => c * tableauBasisVec T S))) := by
  rw [youngAdjacentOperator_smul a c (tableauBasisVec T),
    youngAdjacentOperator_smul b c
      (youngAdjacentOperator a (tableauBasisVec T)),
    youngAdjacentOperator_smul a c
      (youngAdjacentOperator b
        (youngAdjacentOperator a (tableauBasisVec T))),
    youngAdjacentOperator_smul b c (tableauBasisVec T),
    youngAdjacentOperator_smul a c
      (youngAdjacentOperator b (tableauBasisVec T)),
    youngAdjacentOperator_smul b c
      (youngAdjacentOperator a
        (youngAdjacentOperator b (tableauBasisVec T))),
    youngAdjacentOperator_braid_basis_of_succ T a b hsucc]

theorem youngAdjacentOperator_braid_of_succ
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (a b : Fin n) (hsucc : (b : Nat) = (a : Nat) + 1)
    (f : TableauSpace lam) :
    youngAdjacentOperator a
        (youngAdjacentOperator b (youngAdjacentOperator a f)) =
      youngAdjacentOperator b
        (youngAdjacentOperator a (youngAdjacentOperator b f)) := by
  classical
  have hf := tableauBasis_expansion f
  calc
    youngAdjacentOperator a
        (youngAdjacentOperator b (youngAdjacentOperator a f))
        = youngAdjacentOperator a
            (youngAdjacentOperator b
              (youngAdjacentOperator a
                (fun S =>
                  ∑ T : StandardYoungTableau lam,
                    f T * tableauBasisVec T S))) := by
            exact congrArg
              (fun g => youngAdjacentOperator a
                (youngAdjacentOperator b (youngAdjacentOperator a g)))
              hf
    _ = youngAdjacentOperator a
          (youngAdjacentOperator b
            (fun S =>
              ∑ T : StandardYoungTableau lam,
                youngAdjacentOperator a
                  (fun S => f T * tableauBasisVec T S) S)) := by
            rw [youngAdjacentOperator_sum]
    _ = youngAdjacentOperator a
          (fun S =>
            ∑ T : StandardYoungTableau lam,
              youngAdjacentOperator b
                (youngAdjacentOperator a
                  (fun S => f T * tableauBasisVec T S)) S) := by
            rw [youngAdjacentOperator_sum]
    _ = (fun S =>
          ∑ T : StandardYoungTableau lam,
            youngAdjacentOperator a
              (youngAdjacentOperator b
                (youngAdjacentOperator a
                  (fun S => f T * tableauBasisVec T S))) S) := by
            rw [youngAdjacentOperator_sum]
    _ = (fun S =>
          ∑ T : StandardYoungTableau lam,
            youngAdjacentOperator b
              (youngAdjacentOperator a
                (youngAdjacentOperator b
                  (fun S => f T * tableauBasisVec T S))) S) := by
            funext S
            apply Finset.sum_congr rfl
            intro T _
            rw [youngAdjacentOperator_braid_smul_basis_of_succ
              T a b hsucc (f T)]
    _ = youngAdjacentOperator b
          (fun S =>
            ∑ T : StandardYoungTableau lam,
              youngAdjacentOperator a
                (youngAdjacentOperator b
                  (fun S => f T * tableauBasisVec T S)) S) := by
            rw [← youngAdjacentOperator_sum]
    _ = youngAdjacentOperator b
          (youngAdjacentOperator a
            (fun S =>
              ∑ T : StandardYoungTableau lam,
                youngAdjacentOperator b
                  (fun S => f T * tableauBasisVec T S) S)) := by
            rw [← youngAdjacentOperator_sum]
    _ = youngAdjacentOperator b
          (youngAdjacentOperator a
            (youngAdjacentOperator b
              (fun S =>
                ∑ T : StandardYoungTableau lam,
                  f T * tableauBasisVec T S))) := by
            rw [← youngAdjacentOperator_sum]
    _ = youngAdjacentOperator b
          (youngAdjacentOperator a (youngAdjacentOperator b f)) := by
            exact congrArg
              (fun g => youngAdjacentOperator b
                (youngAdjacentOperator a (youngAdjacentOperator b g)))
              hf.symm

/-- The diagonal content operator in the tableau coordinate basis. -/
noncomputable def jucysMurphyDiagonalOperator {n : Nat}
    {lam : YoungDiagram n} (a : Fin n) :
    TableauSpace lam -> TableauSpace lam :=
  fun f T => (entryContent T a : ℝ) * f T

theorem jucysMurphyDiagonalOperator_basis_self {n : Nat}
    {lam : YoungDiagram n}
    (T : StandardYoungTableau lam) (a : Fin n) :
    jucysMurphyDiagonalOperator a (tableauBasisVec T) T =
      (entryContent T a : ℝ) := by
  simp [jucysMurphyDiagonalOperator, tableauBasisVec]

theorem jucysMurphyDiagonalOperator_basis_ne {n : Nat}
    {lam : YoungDiagram n}
    {S T : StandardYoungTableau lam} (a : Fin n)
    (hST : S ≠ T) :
    jucysMurphyDiagonalOperator a (tableauBasisVec T) S = 0 := by
  simp [jucysMurphyDiagonalOperator, tableauBasisVec, hST]

theorem jucysMurphyDiagonalOperator_basis_eigen {n : Nat}
    {lam : YoungDiagram n}
    (T : StandardYoungTableau lam) (a : Fin n) :
    jucysMurphyDiagonalOperator a (tableauBasisVec T) =
      fun S => (entryContent T a : ℝ) * tableauBasisVec T S := by
  funext S
  by_cases hST : S = T
  · subst S
    simp [jucysMurphyDiagonalOperator, tableauBasisVec]
  · simp [jucysMurphyDiagonalOperator, tableauBasisVec, hST]

end DictatorshipTesting
