import AlgebraicLibrary.Young.StandardTableau

noncomputable section

namespace AlgebraicLibrary

/-- The lower entry in an adjacent pair, viewed in `Fin (n+1)`. -/
def adjacentEntryLo {n : Nat} (a : Fin n) : Fin (n + 1) :=
  Fin.castSucc a

/-- The upper entry in an adjacent pair, viewed in `Fin (n+1)`. -/
def adjacentEntryHi {n : Nat} (a : Fin n) : Fin (n + 1) :=
  ⟨(a : Nat) + 1, by
    have ha := a.isLt
    omega⟩

theorem adjacentEntryLo_val {n : Nat} (a : Fin n) :
    (adjacentEntryLo a : Nat) = a := by
  rfl

theorem adjacentEntryHi_val {n : Nat} (a : Fin n) :
    (adjacentEntryHi a : Nat) = (a : Nat) + 1 := by
  rfl

theorem adjacentEntryHi_eq_lo_of_succ {n : Nat}
    (a b : Fin n) (hsucc : (b : Nat) = (a : Nat) + 1) :
    adjacentEntryHi a = adjacentEntryLo b := by
  apply Fin.ext
  simp [adjacentEntryHi, adjacentEntryLo, hsucc]

theorem adjacentEntryLo_ne_hi {n : Nat} (a : Fin n) :
    adjacentEntryLo a ≠ adjacentEntryHi a := by
  intro h
  have hval := congrArg Fin.val h
  simp [adjacentEntryLo, adjacentEntryHi] at hval

/-- Cell of the lower entry in an adjacent pair. -/
noncomputable def adjacentLoCell {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) : YoungCell lam :=
  cellOfEntry T (adjacentEntryLo a)

/-- Cell of the upper entry in an adjacent pair. -/
noncomputable def adjacentHiCell {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) : YoungCell lam :=
  cellOfEntry T (adjacentEntryHi a)

theorem entry_adjacentLoCell {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) :
    T.entry (adjacentLoCell T a) = adjacentEntryLo a := by
  exact entry_cellOfEntry T (adjacentEntryLo a)

theorem entry_adjacentHiCell {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) :
    T.entry (adjacentHiCell T a) = adjacentEntryHi a := by
  exact entry_cellOfEntry T (adjacentEntryHi a)

theorem adjacentHiCell_eq_loCell_of_succ {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hsucc : (b : Nat) = (a : Nat) + 1) :
    adjacentHiCell T a = adjacentLoCell T b := by
  apply T.bijective.1
  rw [entry_adjacentHiCell, entry_adjacentLoCell,
    adjacentEntryHi_eq_lo_of_succ a b hsucc]

theorem adjacentLoCell_ne_hiCell {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) :
    adjacentLoCell T a ≠ adjacentHiCell T a := by
  intro hcell
  have hentry :
      adjacentEntryLo a = adjacentEntryHi a := by
    rw [← entry_adjacentLoCell T a, ← entry_adjacentHiCell T a, hcell]
  exact adjacentEntryLo_ne_hi a hentry

/-- If adjacent entries lie in the same row, the lower entry is to the left. -/
theorem adjacent_col_lt_of_sameRow {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow :
      YoungCell.row (adjacentLoCell T a) =
        YoungCell.row (adjacentHiCell T a)) :
    YoungCell.col (adjacentLoCell T a) <
      YoungCell.col (adjacentHiCell T a) := by
  let lo := adjacentLoCell T a
  let hi := adjacentHiCell T a
  have hcell_ne : lo ≠ hi := by
    simpa [lo, hi] using adjacentLoCell_ne_hiCell T a
  have hcol_ne : YoungCell.col lo ≠ YoungCell.col hi := by
    intro hcol
    apply hcell_ne
    exact YoungCell.ext_row_col (by simpa [lo, hi] using hrow) hcol
  by_cases hlt : YoungCell.col lo < YoungCell.col hi
  · exact hlt
  · have hrev : YoungCell.col hi < YoungCell.col lo := by
      have hle : YoungCell.col hi <= YoungCell.col lo :=
        Nat.le_of_not_gt hlt
      omega
    have hstrict : T.entry hi < T.entry lo := by
      apply T.row_strict
      · simpa [lo, hi] using hrow.symm
      · exact hrev
    have hval : (T.entry hi : Nat) < (T.entry lo : Nat) := hstrict
    rw [show T.entry hi = adjacentEntryHi a by
        simpa [hi] using entry_adjacentHiCell T a,
      show T.entry lo = adjacentEntryLo a by
        simpa [lo] using entry_adjacentLoCell T a] at hval
    simp [adjacentEntryHi, adjacentEntryLo] at hval

/-- If adjacent entries lie in the same column, the lower entry is above. -/
theorem adjacent_row_lt_of_sameCol {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol :
      YoungCell.col (adjacentLoCell T a) =
        YoungCell.col (adjacentHiCell T a)) :
    YoungCell.row (adjacentLoCell T a) <
      YoungCell.row (adjacentHiCell T a) := by
  let lo := adjacentLoCell T a
  let hi := adjacentHiCell T a
  have hcell_ne : lo ≠ hi := by
    simpa [lo, hi] using adjacentLoCell_ne_hiCell T a
  have hrow_ne : YoungCell.row lo ≠ YoungCell.row hi := by
    intro hrow
    apply hcell_ne
    exact YoungCell.ext_row_col hrow (by simpa [lo, hi] using hcol)
  by_cases hlt : YoungCell.row lo < YoungCell.row hi
  · exact hlt
  · have hrev : YoungCell.row hi < YoungCell.row lo := by
      have hle : YoungCell.row hi <= YoungCell.row lo :=
        Nat.le_of_not_gt hlt
      omega
    have hstrict : T.entry hi < T.entry lo := by
      apply T.col_strict
      · simpa [lo, hi] using hcol.symm
      · exact hrev
    have hval : (T.entry hi : Nat) < (T.entry lo : Nat) := hstrict
    rw [show T.entry hi = adjacentEntryHi a by
        simpa [hi] using entry_adjacentHiCell T a,
      show T.entry lo = adjacentEntryLo a by
        simpa [lo] using entry_adjacentLoCell T a] at hval
    simp [adjacentEntryHi, adjacentEntryLo] at hval

/-- If adjacent entries lie in the same row, then the upper entry is exactly
one column to the right. -/
theorem adjacent_col_eq_succ_of_sameRow {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow :
      YoungCell.row (adjacentLoCell T a) =
        YoungCell.row (adjacentHiCell T a)) :
    YoungCell.col (adjacentHiCell T a) =
      YoungCell.col (adjacentLoCell T a) + 1 := by
  let lo := adjacentLoCell T a
  let hi := adjacentHiCell T a
  have hlt : YoungCell.col lo < YoungCell.col hi := by
    simpa [lo, hi] using adjacent_col_lt_of_sameRow T a hrow
  by_cases hgap : YoungCell.col lo + 1 < YoungCell.col hi
  · have hhi_box : YoungCell.col hi < youngRow lam (YoungCell.row hi) := by
      simpa [YoungCell.toNatPair, IsYoungBox] using YoungCell.isYoungBox hi
    have hmid_cell :
        YoungCell.col lo + 1 < youngRow lam (YoungCell.row lo) := by
      rw [show YoungCell.row lo = YoungCell.row hi by
        simpa [lo, hi] using hrow]
      omega
    let mid : YoungCell lam :=
      youngCellOfNat lam (YoungCell.row lo) (YoungCell.col lo + 1) hmid_cell
    have hmid_row : YoungCell.row mid = YoungCell.row lo := by
      simp [mid, youngCellOfNat_row]
    have hmid_col : YoungCell.col mid = YoungCell.col lo + 1 := by
      simp [mid, youngCellOfNat_col]
    have hlo_mid : T.entry lo < T.entry mid := by
      apply T.row_strict
      · exact hmid_row.symm
      · rw [hmid_col]
        omega
    have hmid_hi : T.entry mid < T.entry hi := by
      apply T.row_strict
      · rw [hmid_row]
        simpa [lo, hi] using hrow
      · rw [hmid_col]
        exact hgap
    have hlo_val : (T.entry lo : Nat) = (a : Nat) := by
      rw [show T.entry lo = adjacentEntryLo a by
        simpa [lo] using entry_adjacentLoCell T a]
      rfl
    have hhi_val : (T.entry hi : Nat) = (a : Nat) + 1 := by
      rw [show T.entry hi = adjacentEntryHi a by
        simpa [hi] using entry_adjacentHiCell T a]
      rfl
    have hlo_mid_val : (T.entry lo : Nat) < (T.entry mid : Nat) := hlo_mid
    have hmid_hi_val : (T.entry mid : Nat) < (T.entry hi : Nat) := hmid_hi
    omega
  · change YoungCell.col hi = YoungCell.col lo + 1
    omega

/-- If adjacent entries lie in the same column, then the upper entry is exactly
one row below. -/
theorem adjacent_row_eq_succ_of_sameCol {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol :
      YoungCell.col (adjacentLoCell T a) =
        YoungCell.col (adjacentHiCell T a)) :
    YoungCell.row (adjacentHiCell T a) =
      YoungCell.row (adjacentLoCell T a) + 1 := by
  let lo := adjacentLoCell T a
  let hi := adjacentHiCell T a
  have hlt : YoungCell.row lo < YoungCell.row hi := by
    simpa [lo, hi] using adjacent_row_lt_of_sameCol T a hcol
  by_cases hgap : YoungCell.row lo + 1 < YoungCell.row hi
  · have hhi_box : YoungCell.col hi < youngRow lam (YoungCell.row hi) := by
      simpa [YoungCell.toNatPair, IsYoungBox] using YoungCell.isYoungBox hi
    have hrow_le :
        youngRow lam (YoungCell.row hi) <=
          youngRow lam (YoungCell.row lo + 1) :=
      youngRow_le_of_le lam (by omega)
    have hmid_cell :
        YoungCell.col lo < youngRow lam (YoungCell.row lo + 1) := by
      rw [show YoungCell.col lo = YoungCell.col hi by
        simpa [lo, hi] using hcol]
      omega
    let mid : YoungCell lam :=
      youngCellOfNat lam (YoungCell.row lo + 1) (YoungCell.col lo) hmid_cell
    have hmid_row : YoungCell.row mid = YoungCell.row lo + 1 := by
      simp [mid, youngCellOfNat_row]
    have hmid_col : YoungCell.col mid = YoungCell.col lo := by
      simp [mid, youngCellOfNat_col]
    have hlo_mid : T.entry lo < T.entry mid := by
      apply T.col_strict
      · exact hmid_col.symm
      · rw [hmid_row]
        omega
    have hmid_hi : T.entry mid < T.entry hi := by
      apply T.col_strict
      · rw [hmid_col]
        simpa [lo, hi] using hcol
      · rw [hmid_row]
        exact hgap
    have hlo_val : (T.entry lo : Nat) = (a : Nat) := by
      rw [show T.entry lo = adjacentEntryLo a by
        simpa [lo] using entry_adjacentLoCell T a]
      rfl
    have hhi_val : (T.entry hi : Nat) = (a : Nat) + 1 := by
      rw [show T.entry hi = adjacentEntryHi a by
        simpa [hi] using entry_adjacentHiCell T a]
      rfl
    have hlo_mid_val : (T.entry lo : Nat) < (T.entry mid : Nat) := hlo_mid
    have hmid_hi_val : (T.entry mid : Nat) < (T.entry hi : Nat) := hmid_hi
    omega
  · change YoungCell.row hi = YoungCell.row lo + 1
    omega

/-- In the same-row case, contents differ by `+1`. -/
theorem adjacent_content_hi_eq_lo_add_one_of_sameRow {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow :
      YoungCell.row (adjacentLoCell T a) =
        YoungCell.row (adjacentHiCell T a)) :
    YoungCell.content (adjacentHiCell T a) =
      YoungCell.content (adjacentLoCell T a) + 1 := by
  unfold YoungCell.content
  have hcol := adjacent_col_eq_succ_of_sameRow T a hrow
  omega

/-- In the same-column case, contents differ by `-1`. -/
theorem adjacent_content_hi_eq_lo_sub_one_of_sameCol {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol :
      YoungCell.col (adjacentLoCell T a) =
        YoungCell.col (adjacentHiCell T a)) :
    YoungCell.content (adjacentHiCell T a) =
      YoungCell.content (adjacentLoCell T a) - 1 := by
  unfold YoungCell.content
  have hrow := adjacent_row_eq_succ_of_sameCol T a hcol
  omega

/-- Swap the two adjacent values `a` and `a+1`, fixing all other values. -/
def adjacentSwapValue {n : Nat} (a : Fin n) (x : Fin (n + 1)) : Fin (n + 1) :=
  if x = adjacentEntryLo a then
    adjacentEntryHi a
  else if x = adjacentEntryHi a then
    adjacentEntryLo a
  else
    x

theorem adjacentSwapValue_lo {n : Nat} (a : Fin n) :
    adjacentSwapValue a (adjacentEntryLo a) = adjacentEntryHi a := by
  simp [adjacentSwapValue]

theorem adjacentSwapValue_hi {n : Nat} (a : Fin n) :
    adjacentSwapValue a (adjacentEntryHi a) = adjacentEntryLo a := by
  simp [adjacentSwapValue, (adjacentEntryLo_ne_hi a).symm]

theorem adjacentSwapValue_of_ne_lo_hi {n : Nat} (a : Fin n) {x : Fin (n + 1)}
    (hlo : x ≠ adjacentEntryLo a) (hhi : x ≠ adjacentEntryHi a) :
    adjacentSwapValue a x = x := by
  simp [adjacentSwapValue, hlo, hhi]

theorem adjacentSwapValue_involutive {n : Nat} (a : Fin n) (x : Fin (n + 1)) :
    adjacentSwapValue a (adjacentSwapValue a x) = x := by
  by_cases hlo : x = adjacentEntryLo a
  · subst x
    rw [adjacentSwapValue_lo, adjacentSwapValue_hi]
  · by_cases hhi : x = adjacentEntryHi a
    · subst x
      rw [adjacentSwapValue_hi, adjacentSwapValue_lo]
    · rw [adjacentSwapValue_of_ne_lo_hi a hlo hhi]
      rw [adjacentSwapValue_of_ne_lo_hi a hlo hhi]

theorem adjacentSwapValue_comm_of_disjoint_entries {n : Nat}
    (a b : Fin n)
    (hlo_lo : adjacentEntryLo a ≠ adjacentEntryLo b)
    (hlo_hi : adjacentEntryLo a ≠ adjacentEntryHi b)
    (hhi_lo : adjacentEntryHi a ≠ adjacentEntryLo b)
    (hhi_hi : adjacentEntryHi a ≠ adjacentEntryHi b)
    (x : Fin (n + 1)) :
    adjacentSwapValue a (adjacentSwapValue b x) =
      adjacentSwapValue b (adjacentSwapValue a x) := by
  by_cases hxa_lo : x = adjacentEntryLo a
  · subst x
    rw [adjacentSwapValue_of_ne_lo_hi b hlo_lo hlo_hi,
      adjacentSwapValue_lo,
      adjacentSwapValue_of_ne_lo_hi b hhi_lo hhi_hi]
  · by_cases hxa_hi : x = adjacentEntryHi a
    · subst x
      rw [adjacentSwapValue_of_ne_lo_hi b hhi_lo hhi_hi,
        adjacentSwapValue_hi,
        adjacentSwapValue_of_ne_lo_hi b hlo_lo hlo_hi]
    · by_cases hxb_lo : x = adjacentEntryLo b
      · subst x
        rw [adjacentSwapValue_lo,
          adjacentSwapValue_of_ne_lo_hi a hlo_hi.symm hhi_hi.symm,
          adjacentSwapValue_of_ne_lo_hi a hlo_lo.symm hhi_lo.symm,
          adjacentSwapValue_lo]
      · by_cases hxb_hi : x = adjacentEntryHi b
        · subst x
          rw [adjacentSwapValue_hi,
            adjacentSwapValue_of_ne_lo_hi a hlo_lo.symm hhi_lo.symm,
            adjacentSwapValue_of_ne_lo_hi a hlo_hi.symm hhi_hi.symm,
            adjacentSwapValue_hi]
        · rw [adjacentSwapValue_of_ne_lo_hi a hxa_lo hxa_hi,
            adjacentSwapValue_of_ne_lo_hi b hxb_lo hxb_hi,
            adjacentSwapValue_of_ne_lo_hi a hxa_lo hxa_hi]

theorem adjacentSwapValue_braid_of_succ {n : Nat}
    (a b : Fin n) (hsucc : (b : Nat) = (a : Nat) + 1)
    (x : Fin (n + 1)) :
    adjacentSwapValue a (adjacentSwapValue b (adjacentSwapValue a x)) =
      adjacentSwapValue b (adjacentSwapValue a (adjacentSwapValue b x)) := by
  have hhi_lo : adjacentEntryHi a = adjacentEntryLo b := by
    apply Fin.ext
    simp [adjacentEntryHi, adjacentEntryLo, hsucc]
  have hlo_ne_lo : adjacentEntryLo a ≠ adjacentEntryLo b := by
    intro h
    have hv := congrArg Fin.val h
    simp [adjacentEntryLo, hsucc] at hv
  have hlo_ne_hi : adjacentEntryLo a ≠ adjacentEntryHi b := by
    intro h
    have hv := congrArg Fin.val h
    simp [adjacentEntryLo, adjacentEntryHi, hsucc] at hv
    omega
  have hhi_ne_hi : adjacentEntryHi a ≠ adjacentEntryHi b := by
    intro h
    have hv := congrArg Fin.val h
    simp [adjacentEntryHi, hsucc] at hv
  by_cases hx_lo : x = adjacentEntryLo a
  · subst x
    rw [adjacentSwapValue_lo,
      show adjacentSwapValue b (adjacentEntryHi a) = adjacentEntryHi b by
        simpa [hhi_lo] using adjacentSwapValue_lo b,
      adjacentSwapValue_of_ne_lo_hi a hlo_ne_hi.symm hhi_ne_hi.symm,
      adjacentSwapValue_of_ne_lo_hi b hlo_ne_lo hlo_ne_hi,
      adjacentSwapValue_lo,
      show adjacentSwapValue b (adjacentEntryHi a) = adjacentEntryHi b by
        simpa [hhi_lo] using adjacentSwapValue_lo b]
  · by_cases hx_hi_a : x = adjacentEntryHi a
    · subst x
      rw [adjacentSwapValue_hi,
        adjacentSwapValue_of_ne_lo_hi b hlo_ne_lo hlo_ne_hi,
        adjacentSwapValue_lo,
        show adjacentSwapValue b (adjacentEntryHi a) = adjacentEntryHi b by
          simpa [hhi_lo] using adjacentSwapValue_lo b,
        adjacentSwapValue_of_ne_lo_hi a hlo_ne_hi.symm hhi_ne_hi.symm,
        adjacentSwapValue_hi]
      exact hhi_lo
    · by_cases hx_hi_b : x = adjacentEntryHi b
      · subst x
        rw [adjacentSwapValue_of_ne_lo_hi a hlo_ne_hi.symm hhi_ne_hi.symm,
          adjacentSwapValue_hi,
          show adjacentSwapValue a (adjacentEntryLo b) = adjacentEntryLo a by
            simpa [← hhi_lo] using adjacentSwapValue_hi a,
          adjacentSwapValue_of_ne_lo_hi b hlo_ne_lo hlo_ne_hi]
      · have hx_lo_b : x ≠ adjacentEntryLo b := by
          intro h
          exact hx_hi_a (by simpa [← hhi_lo] using h)
        rw [adjacentSwapValue_of_ne_lo_hi a hx_lo hx_hi_a,
          adjacentSwapValue_of_ne_lo_hi b hx_lo_b hx_hi_b,
          adjacentSwapValue_of_ne_lo_hi a hx_lo hx_hi_a,
          adjacentSwapValue_of_ne_lo_hi b hx_lo_b hx_hi_b]

/-- Two adjacent-index swaps have disjoint supports when the two adjacent pairs
of labels are separated by at least one label. -/
def adjacentIndexDisjoint {n : Nat} (a b : Fin n) : Prop :=
  (a : Nat) + 1 < (b : Nat) ∨ (b : Nat) + 1 < (a : Nat)

theorem adjacentIndexDisjoint_symm {n : Nat} {a b : Fin n}
    (hdisj : adjacentIndexDisjoint a b) :
    adjacentIndexDisjoint b a := by
  rcases hdisj with hdisj | hdisj
  · exact Or.inr hdisj
  · exact Or.inl hdisj

theorem adjacentEntryLo_ne_lo_of_disjoint_indices {n : Nat}
    (a b : Fin n) (hdisj : adjacentIndexDisjoint a b) :
    adjacentEntryLo a ≠ adjacentEntryLo b := by
  intro h
  have hv := congrArg Fin.val h
  rcases hdisj with hdisj | hdisj
  · simp [adjacentEntryLo] at hv
    omega
  · simp [adjacentEntryLo] at hv
    omega

theorem adjacentEntryLo_ne_hi_of_disjoint_indices {n : Nat}
    (a b : Fin n) (hdisj : adjacentIndexDisjoint a b) :
    adjacentEntryLo a ≠ adjacentEntryHi b := by
  intro h
  have hv := congrArg Fin.val h
  rcases hdisj with hdisj | hdisj
  · simp [adjacentEntryLo, adjacentEntryHi] at hv
    omega
  · simp [adjacentEntryLo, adjacentEntryHi] at hv
    omega

theorem adjacentEntryHi_ne_lo_of_disjoint_indices {n : Nat}
    (a b : Fin n) (hdisj : adjacentIndexDisjoint a b) :
    adjacentEntryHi a ≠ adjacentEntryLo b := by
  intro h
  have hv := congrArg Fin.val h
  rcases hdisj with hdisj | hdisj
  · simp [adjacentEntryLo, adjacentEntryHi] at hv
    omega
  · simp [adjacentEntryLo, adjacentEntryHi] at hv
    omega

theorem adjacentEntryHi_ne_hi_of_disjoint_indices {n : Nat}
    (a b : Fin n) (hdisj : adjacentIndexDisjoint a b) :
    adjacentEntryHi a ≠ adjacentEntryHi b := by
  intro h
  have hv := congrArg Fin.val h
  rcases hdisj with hdisj | hdisj
  · simp [adjacentEntryHi] at hv
    omega
  · simp [adjacentEntryHi] at hv
    omega

theorem adjacentSwapValue_comm_of_disjoint_indices {n : Nat}
    (a b : Fin n) (hdisj : adjacentIndexDisjoint a b)
    (x : Fin (n + 1)) :
    adjacentSwapValue a (adjacentSwapValue b x) =
      adjacentSwapValue b (adjacentSwapValue a x) := by
  apply adjacentSwapValue_comm_of_disjoint_entries
  · exact adjacentEntryLo_ne_lo_of_disjoint_indices a b hdisj
  · exact adjacentEntryLo_ne_hi_of_disjoint_indices a b hdisj
  · exact adjacentEntryHi_ne_lo_of_disjoint_indices a b hdisj
  · exact adjacentEntryHi_ne_hi_of_disjoint_indices a b hdisj

/-- Entry function obtained by swapping the two adjacent values. -/
def adjacentSwapEntry {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) :
    YoungCell lam -> Fin (n + 1) :=
  fun u => adjacentSwapValue a (T.entry u)

theorem adjacentSwapEntry_loCell {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) :
    adjacentSwapEntry T a (adjacentLoCell T a) = adjacentEntryHi a := by
  rw [adjacentSwapEntry, entry_adjacentLoCell, adjacentSwapValue_lo]

theorem adjacentSwapEntry_hiCell {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) :
    adjacentSwapEntry T a (adjacentHiCell T a) = adjacentEntryLo a := by
  rw [adjacentSwapEntry, entry_adjacentHiCell, adjacentSwapValue_hi]

theorem adjacentSwapEntry_of_ne_lo_hi {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) {u : YoungCell lam}
    (hlo : T.entry u ≠ adjacentEntryLo a)
    (hhi : T.entry u ≠ adjacentEntryHi a) :
    adjacentSwapEntry T a u = T.entry u := by
  rw [adjacentSwapEntry, adjacentSwapValue_of_ne_lo_hi a hlo hhi]

theorem adjacentSwapEntry_involutive {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) (u : YoungCell lam) :
    adjacentSwapValue a (adjacentSwapEntry T a u) = T.entry u := by
  rw [adjacentSwapEntry, adjacentSwapValue_involutive]

theorem adjacentSwapEntry_comm_of_disjoint_indices {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hdisj : adjacentIndexDisjoint a b) (u : YoungCell lam) :
    adjacentSwapValue a (adjacentSwapEntry T b u) =
      adjacentSwapValue b (adjacentSwapEntry T a u) := by
  rw [adjacentSwapEntry, adjacentSwapEntry]
  exact adjacentSwapValue_comm_of_disjoint_indices a b hdisj (T.entry u)

theorem adjacentSwapEntry_braid_of_succ {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hsucc : (b : Nat) = (a : Nat) + 1) (u : YoungCell lam) :
    adjacentSwapValue a (adjacentSwapValue b (adjacentSwapEntry T a u)) =
      adjacentSwapValue b (adjacentSwapValue a (adjacentSwapEntry T b u)) := by
  rw [adjacentSwapEntry, adjacentSwapEntry]
  exact adjacentSwapValue_braid_of_succ a b hsucc (T.entry u)

theorem adjacentSwapEntry_bijective {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) :
    Function.Bijective (adjacentSwapEntry T a) := by
  constructor
  · intro u v huv
    apply T.bijective.1
    have hswap := congrArg (adjacentSwapValue a) huv
    simpa [adjacentSwapEntry, adjacentSwapValue_involutive] using hswap
  · intro y
    rcases T.bijective.2 (adjacentSwapValue a y) with ⟨u, hu⟩
    refine ⟨u, ?_⟩
    rw [adjacentSwapEntry, hu, adjacentSwapValue_involutive]

theorem adjacentSwapValue_lt_of_lt_of_not_adjacent_pair {n : Nat}
    (a : Fin n) {x y : Fin (n + 1)}
    (hxy : x < y)
    (hpair : ¬ (x = adjacentEntryLo a ∧ y = adjacentEntryHi a)) :
    adjacentSwapValue a x < adjacentSwapValue a y := by
  by_cases hxlo : x = adjacentEntryLo a
  · subst x
    by_cases hyhi : y = adjacentEntryHi a
    · exact False.elim (hpair ⟨rfl, hyhi⟩)
    · have hylo : y ≠ adjacentEntryLo a := by
        intro hylo
        subst y
        exact (lt_irrefl _ hxy)
      rw [adjacentSwapValue_lo, adjacentSwapValue_of_ne_lo_hi a hylo hyhi]
      change (adjacentEntryHi a : Nat) < (y : Nat)
      have hxyv : (adjacentEntryLo a : Nat) < (y : Nat) := hxy
      have hyhi_val : (y : Nat) ≠ (a : Nat) + 1 := by
        intro hyval
        apply hyhi
        apply Fin.ext
        simpa [adjacentEntryHi] using hyval
      simp [adjacentEntryLo, adjacentEntryHi] at hxyv ⊢
      omega
  · by_cases hxhi : x = adjacentEntryHi a
    · subst x
      have hylo : y ≠ adjacentEntryLo a := by
        intro hylo
        subst y
        have hxyv : (adjacentEntryHi a : Nat) < (adjacentEntryLo a : Nat) := hxy
        simp [adjacentEntryLo, adjacentEntryHi] at hxyv
      have hyhi : y ≠ adjacentEntryHi a := by
        intro hyhi
        subst y
        exact (lt_irrefl _ hxy)
      rw [adjacentSwapValue_hi, adjacentSwapValue_of_ne_lo_hi a hylo hyhi]
      change (adjacentEntryLo a : Nat) < (y : Nat)
      have hxyv : (adjacentEntryHi a : Nat) < (y : Nat) := hxy
      simp [adjacentEntryLo, adjacentEntryHi] at hxyv ⊢
      omega
    · by_cases hylo : y = adjacentEntryLo a
      · subst y
        rw [adjacentSwapValue_of_ne_lo_hi a hxlo hxhi, adjacentSwapValue_lo]
        change (x : Nat) < (adjacentEntryHi a : Nat)
        have hxyv : (x : Nat) < (adjacentEntryLo a : Nat) := hxy
        simp [adjacentEntryLo, adjacentEntryHi] at hxyv ⊢
        omega
      · by_cases hyhi : y = adjacentEntryHi a
        · subst y
          rw [adjacentSwapValue_of_ne_lo_hi a hxlo hxhi, adjacentSwapValue_hi]
          change (x : Nat) < (adjacentEntryLo a : Nat)
          have hxyv : (x : Nat) < (adjacentEntryHi a : Nat) := hxy
          have hxlo_val : (x : Nat) ≠ (a : Nat) := by
            intro hxval
            apply hxlo
            apply Fin.ext
            simpa [adjacentEntryLo] using hxval
          simp [adjacentEntryLo, adjacentEntryHi] at hxyv ⊢
          omega
        · rw [adjacentSwapValue_of_ne_lo_hi a hxlo hxhi,
            adjacentSwapValue_of_ne_lo_hi a hylo hyhi]
          exact hxy

noncomputable def adjacentSwapTableau {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne :
      YoungCell.row (adjacentLoCell T a) ≠
        YoungCell.row (adjacentHiCell T a))
    (hcol_ne :
      YoungCell.col (adjacentLoCell T a) ≠
        YoungCell.col (adjacentHiCell T a)) :
    StandardYoungTableau lam where
  entry := adjacentSwapEntry T a
  bijective := adjacentSwapEntry_bijective T a
  row_strict := by
    intro u v hrow hcol
    apply adjacentSwapValue_lt_of_lt_of_not_adjacent_pair a
    · exact T.row_strict hrow hcol
    · intro hpair
      rcases hpair with ⟨hu_entry, hv_entry⟩
      have hu_cell : adjacentLoCell T a = u :=
        cellOfEntry_eq_of_entry T hu_entry
      have hv_cell : adjacentHiCell T a = v :=
        cellOfEntry_eq_of_entry T hv_entry
      apply hrow_ne
      rw [hu_cell, hv_cell]
      exact hrow
  col_strict := by
    intro u v hcol hrow
    apply adjacentSwapValue_lt_of_lt_of_not_adjacent_pair a
    · exact T.col_strict hcol hrow
    · intro hpair
      rcases hpair with ⟨hu_entry, hv_entry⟩
      have hu_cell : adjacentLoCell T a = u :=
        cellOfEntry_eq_of_entry T hu_entry
      have hv_cell : adjacentHiCell T a = v :=
        cellOfEntry_eq_of_entry T hv_entry
      apply hcol_ne
      rw [hu_cell, hv_cell]
      exact hcol

theorem adjacentSwapTableau_comm_of_disjoint_indices {n : Nat}
    {lam : YoungDiagram (n + 1)}
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
        YoungCell.col (adjacentHiCell T b))
    (hrow_a_after_b :
      YoungCell.row (adjacentLoCell
          (adjacentSwapTableau T b hrow_b hcol_b) a) ≠
        YoungCell.row (adjacentHiCell
          (adjacentSwapTableau T b hrow_b hcol_b) a))
    (hcol_a_after_b :
      YoungCell.col (adjacentLoCell
          (adjacentSwapTableau T b hrow_b hcol_b) a) ≠
        YoungCell.col (adjacentHiCell
          (adjacentSwapTableau T b hrow_b hcol_b) a))
    (hrow_b_after_a :
      YoungCell.row (adjacentLoCell
          (adjacentSwapTableau T a hrow_a hcol_a) b) ≠
        YoungCell.row (adjacentHiCell
          (adjacentSwapTableau T a hrow_a hcol_a) b))
    (hcol_b_after_a :
      YoungCell.col (adjacentLoCell
          (adjacentSwapTableau T a hrow_a hcol_a) b) ≠
        YoungCell.col (adjacentHiCell
          (adjacentSwapTableau T a hrow_a hcol_a) b)) :
    adjacentSwapTableau
        (adjacentSwapTableau T b hrow_b hcol_b) a
        hrow_a_after_b hcol_a_after_b =
      adjacentSwapTableau
        (adjacentSwapTableau T a hrow_a hcol_a) b
        hrow_b_after_a hcol_b_after_a := by
  apply standardYoungTableau_ext_entry
  intro u
  change
    adjacentSwapValue a (adjacentSwapEntry T b u) =
      adjacentSwapValue b (adjacentSwapEntry T a u)
  exact adjacentSwapEntry_comm_of_disjoint_indices T a b hdisj u

theorem adjacentSwapTableau_cell_lo {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne :
      YoungCell.row (adjacentLoCell T a) ≠
        YoungCell.row (adjacentHiCell T a))
    (hcol_ne :
      YoungCell.col (adjacentLoCell T a) ≠
        YoungCell.col (adjacentHiCell T a)) :
    cellOfEntry (adjacentSwapTableau T a hrow_ne hcol_ne) (adjacentEntryLo a) =
      adjacentHiCell T a := by
  apply cellOfEntry_eq_of_entry
  exact adjacentSwapEntry_hiCell T a

theorem adjacentSwapTableau_cell_hi {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne :
      YoungCell.row (adjacentLoCell T a) ≠
        YoungCell.row (adjacentHiCell T a))
    (hcol_ne :
      YoungCell.col (adjacentLoCell T a) ≠
        YoungCell.col (adjacentHiCell T a)) :
    cellOfEntry (adjacentSwapTableau T a hrow_ne hcol_ne) (adjacentEntryHi a) =
      adjacentLoCell T a := by
  apply cellOfEntry_eq_of_entry
  exact adjacentSwapEntry_loCell T a

theorem adjacentSwapTableau_cell_of_ne_lo_hi {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne :
      YoungCell.row (adjacentLoCell T a) ≠
        YoungCell.row (adjacentHiCell T a))
    (hcol_ne :
      YoungCell.col (adjacentLoCell T a) ≠
        YoungCell.col (adjacentHiCell T a))
    {b : Fin (n + 1)}
    (hblo : b ≠ adjacentEntryLo a)
    (hbhi : b ≠ adjacentEntryHi a) :
    cellOfEntry (adjacentSwapTableau T a hrow_ne hcol_ne) b =
      cellOfEntry T b := by
  apply cellOfEntry_eq_of_entry
  have hentry : T.entry (cellOfEntry T b) = b := entry_cellOfEntry T b
  have hlo : T.entry (cellOfEntry T b) ≠ adjacentEntryLo a := by
    rw [hentry]
    exact hblo
  have hhi : T.entry (cellOfEntry T b) ≠ adjacentEntryHi a := by
    rw [hentry]
    exact hbhi
  rw [adjacentSwapTableau]
  exact (adjacentSwapEntry_of_ne_lo_hi T a hlo hhi).trans hentry

theorem adjacentSwapTableau_cell_lo_of_disjoint_indices {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hdisj : adjacentIndexDisjoint a b)
    (hrow_b :
      YoungCell.row (adjacentLoCell T b) ≠
        YoungCell.row (adjacentHiCell T b))
    (hcol_b :
      YoungCell.col (adjacentLoCell T b) ≠
        YoungCell.col (adjacentHiCell T b)) :
    cellOfEntry (adjacentSwapTableau T b hrow_b hcol_b)
        (adjacentEntryLo a) =
      adjacentLoCell T a := by
  exact adjacentSwapTableau_cell_of_ne_lo_hi T b hrow_b hcol_b
    (adjacentEntryLo_ne_lo_of_disjoint_indices a b hdisj)
    (adjacentEntryLo_ne_hi_of_disjoint_indices a b hdisj)

theorem adjacentSwapTableau_cell_hi_of_disjoint_indices {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hdisj : adjacentIndexDisjoint a b)
    (hrow_b :
      YoungCell.row (adjacentLoCell T b) ≠
        YoungCell.row (adjacentHiCell T b))
    (hcol_b :
      YoungCell.col (adjacentLoCell T b) ≠
        YoungCell.col (adjacentHiCell T b)) :
    cellOfEntry (adjacentSwapTableau T b hrow_b hcol_b)
        (adjacentEntryHi a) =
      adjacentHiCell T a := by
  exact adjacentSwapTableau_cell_of_ne_lo_hi T b hrow_b hcol_b
    (adjacentEntryHi_ne_lo_of_disjoint_indices a b hdisj)
    (adjacentEntryHi_ne_hi_of_disjoint_indices a b hdisj)

theorem adjacentSameRow_after_disjoint_swap_iff {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hdisj : adjacentIndexDisjoint a b)
    (hrow_b :
      YoungCell.row (adjacentLoCell T b) ≠
        YoungCell.row (adjacentHiCell T b))
    (hcol_b :
      YoungCell.col (adjacentLoCell T b) ≠
        YoungCell.col (adjacentHiCell T b)) :
    YoungCell.row (adjacentLoCell
        (adjacentSwapTableau T b hrow_b hcol_b) a) =
      YoungCell.row (adjacentHiCell
        (adjacentSwapTableau T b hrow_b hcol_b) a) ↔
    YoungCell.row (adjacentLoCell T a) =
      YoungCell.row (adjacentHiCell T a) := by
  unfold adjacentLoCell adjacentHiCell
  rw [adjacentSwapTableau_cell_lo_of_disjoint_indices T a b hdisj hrow_b hcol_b,
    adjacentSwapTableau_cell_hi_of_disjoint_indices T a b hdisj hrow_b hcol_b]
  rfl

theorem adjacentSameCol_after_disjoint_swap_iff {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hdisj : adjacentIndexDisjoint a b)
    (hrow_b :
      YoungCell.row (adjacentLoCell T b) ≠
        YoungCell.row (adjacentHiCell T b))
    (hcol_b :
      YoungCell.col (adjacentLoCell T b) ≠
        YoungCell.col (adjacentHiCell T b)) :
    YoungCell.col (adjacentLoCell
        (adjacentSwapTableau T b hrow_b hcol_b) a) =
      YoungCell.col (adjacentHiCell
        (adjacentSwapTableau T b hrow_b hcol_b) a) ↔
    YoungCell.col (adjacentLoCell T a) =
      YoungCell.col (adjacentHiCell T a) := by
  unfold adjacentLoCell adjacentHiCell
  rw [adjacentSwapTableau_cell_lo_of_disjoint_indices T a b hdisj hrow_b hcol_b,
    adjacentSwapTableau_cell_hi_of_disjoint_indices T a b hdisj hrow_b hcol_b]
  rfl

theorem adjacentSwapTableau_comm_of_disjoint_indices_auto {n : Nat}
    {lam : YoungDiagram (n + 1)}
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
    adjacentSwapTableau
        (adjacentSwapTableau T b hrow_b hcol_b) a
        (by
          intro h
          exact hrow_a
            ((adjacentSameRow_after_disjoint_swap_iff T a b hdisj
              hrow_b hcol_b).1 h))
        (by
          intro h
          exact hcol_a
            ((adjacentSameCol_after_disjoint_swap_iff T a b hdisj
              hrow_b hcol_b).1 h)) =
      adjacentSwapTableau
        (adjacentSwapTableau T a hrow_a hcol_a) b
        (by
          intro h
          exact hrow_b
            ((adjacentSameRow_after_disjoint_swap_iff T b a
              (adjacentIndexDisjoint_symm hdisj) hrow_a hcol_a).1 h))
        (by
          intro h
          exact hcol_b
            ((adjacentSameCol_after_disjoint_swap_iff T b a
              (adjacentIndexDisjoint_symm hdisj) hrow_a hcol_a).1 h)) := by
  apply standardYoungTableau_ext_entry
  intro u
  change
    adjacentSwapValue a (adjacentSwapEntry T b u) =
      adjacentSwapValue b (adjacentSwapEntry T a u)
  exact adjacentSwapEntry_comm_of_disjoint_indices T a b hdisj u

theorem adjacentSwapTableau_braid_of_succ {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hsucc : (b : Nat) = (a : Nat) + 1)
    (hrow_a :
      YoungCell.row (adjacentLoCell T a) ≠
        YoungCell.row (adjacentHiCell T a))
    (hcol_a :
      YoungCell.col (adjacentLoCell T a) ≠
        YoungCell.col (adjacentHiCell T a))
    (hrow_b_after_a :
      YoungCell.row (adjacentLoCell
          (adjacentSwapTableau T a hrow_a hcol_a) b) ≠
        YoungCell.row (adjacentHiCell
          (adjacentSwapTableau T a hrow_a hcol_a) b))
    (hcol_b_after_a :
      YoungCell.col (adjacentLoCell
          (adjacentSwapTableau T a hrow_a hcol_a) b) ≠
        YoungCell.col (adjacentHiCell
          (adjacentSwapTableau T a hrow_a hcol_a) b))
    (hrow_a_after_b_after_a :
      YoungCell.row (adjacentLoCell
          (adjacentSwapTableau
            (adjacentSwapTableau T a hrow_a hcol_a) b
            hrow_b_after_a hcol_b_after_a) a) ≠
        YoungCell.row (adjacentHiCell
          (adjacentSwapTableau
            (adjacentSwapTableau T a hrow_a hcol_a) b
            hrow_b_after_a hcol_b_after_a) a))
    (hcol_a_after_b_after_a :
      YoungCell.col (adjacentLoCell
          (adjacentSwapTableau
            (adjacentSwapTableau T a hrow_a hcol_a) b
            hrow_b_after_a hcol_b_after_a) a) ≠
        YoungCell.col (adjacentHiCell
          (adjacentSwapTableau
            (adjacentSwapTableau T a hrow_a hcol_a) b
            hrow_b_after_a hcol_b_after_a) a))
    (hrow_b :
      YoungCell.row (adjacentLoCell T b) ≠
        YoungCell.row (adjacentHiCell T b))
    (hcol_b :
      YoungCell.col (adjacentLoCell T b) ≠
        YoungCell.col (adjacentHiCell T b))
    (hrow_a_after_b :
      YoungCell.row (adjacentLoCell
          (adjacentSwapTableau T b hrow_b hcol_b) a) ≠
        YoungCell.row (adjacentHiCell
          (adjacentSwapTableau T b hrow_b hcol_b) a))
    (hcol_a_after_b :
      YoungCell.col (adjacentLoCell
          (adjacentSwapTableau T b hrow_b hcol_b) a) ≠
        YoungCell.col (adjacentHiCell
          (adjacentSwapTableau T b hrow_b hcol_b) a))
    (hrow_b_after_a_after_b :
      YoungCell.row (adjacentLoCell
          (adjacentSwapTableau
            (adjacentSwapTableau T b hrow_b hcol_b) a
            hrow_a_after_b hcol_a_after_b) b) ≠
        YoungCell.row (adjacentHiCell
          (adjacentSwapTableau
            (adjacentSwapTableau T b hrow_b hcol_b) a
            hrow_a_after_b hcol_a_after_b) b))
    (hcol_b_after_a_after_b :
      YoungCell.col (adjacentLoCell
          (adjacentSwapTableau
            (adjacentSwapTableau T b hrow_b hcol_b) a
            hrow_a_after_b hcol_a_after_b) b) ≠
        YoungCell.col (adjacentHiCell
          (adjacentSwapTableau
            (adjacentSwapTableau T b hrow_b hcol_b) a
            hrow_a_after_b hcol_a_after_b) b)) :
    adjacentSwapTableau
        (adjacentSwapTableau
          (adjacentSwapTableau T a hrow_a hcol_a) b
          hrow_b_after_a hcol_b_after_a) a
        hrow_a_after_b_after_a hcol_a_after_b_after_a =
      adjacentSwapTableau
        (adjacentSwapTableau
          (adjacentSwapTableau T b hrow_b hcol_b) a
          hrow_a_after_b hcol_a_after_b) b
        hrow_b_after_a_after_b hcol_b_after_a_after_b := by
  apply standardYoungTableau_ext_entry
  intro u
  change
    adjacentSwapValue a (adjacentSwapValue b (adjacentSwapEntry T a u)) =
      adjacentSwapValue b (adjacentSwapValue a (adjacentSwapEntry T b u))
  exact adjacentSwapEntry_braid_of_succ T a b hsucc u

theorem adjacentSwapTableau_entryContent_lo {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne :
      YoungCell.row (adjacentLoCell T a) ≠
        YoungCell.row (adjacentHiCell T a))
    (hcol_ne :
      YoungCell.col (adjacentLoCell T a) ≠
        YoungCell.col (adjacentHiCell T a)) :
    entryContent (adjacentSwapTableau T a hrow_ne hcol_ne) (adjacentEntryLo a) =
  entryContent T (adjacentEntryHi a) := by
  unfold entryContent
  rw [adjacentSwapTableau_cell_lo]
  simp [adjacentHiCell]

theorem adjacentSwapTableau_entryContent_hi {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne :
      YoungCell.row (adjacentLoCell T a) ≠
        YoungCell.row (adjacentHiCell T a))
    (hcol_ne :
      YoungCell.col (adjacentLoCell T a) ≠
        YoungCell.col (adjacentHiCell T a)) :
    entryContent (adjacentSwapTableau T a hrow_ne hcol_ne) (adjacentEntryHi a) =
  entryContent T (adjacentEntryLo a) := by
  unfold entryContent
  rw [adjacentSwapTableau_cell_hi]
  simp [adjacentLoCell]

theorem adjacentSwapTableau_entryContent_of_ne_lo_hi {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne :
      YoungCell.row (adjacentLoCell T a) ≠
        YoungCell.row (adjacentHiCell T a))
    (hcol_ne :
      YoungCell.col (adjacentLoCell T a) ≠
        YoungCell.col (adjacentHiCell T a))
    {b : Fin (n + 1)}
    (hblo : b ≠ adjacentEntryLo a)
    (hbhi : b ≠ adjacentEntryHi a) :
    entryContent (adjacentSwapTableau T a hrow_ne hcol_ne) b =
      entryContent T b := by
  unfold entryContent
  rw [adjacentSwapTableau_cell_of_ne_lo_hi T a hrow_ne hcol_ne hblo hbhi]

end AlgebraicLibrary
