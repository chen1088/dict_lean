import DictatorshipTesting.Paper.S05_Lem5_06_AdjacentTranspositionsInYoungsBasis

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_16_OneBoxDeletionIntertwinesEarlierSwaps`
-/


/-!
Paper statement: Lemma 5.7 (`lem:jucys-murphy-eigenbasis`), rewritten
Section 5 form.
Title in paper: Diagonal content eigenspaces.

Status: proven. Proved internally for the explicit diagonal content operators.  The
content sequence determines a standard tableau, distinct tableaux differ in a
content coordinate, and the common eigenspaces are the tableau basis lines.
Appendix A.2 remains the external group-algebra Jucys--Murphy identification.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.7 basis-level vocabulary: content of a tableau cell. -/
def S05_Lem5_07_cellContent {n : Nat} {lam : YoungDiagram n}
    (u : YoungCell lam) : Int :=
  YoungCell.content u

/-- Lemma 5.7 basis-level vocabulary: content of the cell containing an entry. -/
noncomputable def S05_Lem5_07_entryContent {n : Nat} {lam : YoungDiagram n}
    (T : StandardYoungTableau lam) (a : Fin n) : Int :=
  entryContent T a

/-- Basis-level content sequence of a standard tableau, indexed by entries. -/
noncomputable def tableauContentSequence {n : Nat} {lam : YoungDiagram n}
    (T : StandardYoungTableau lam) : Fin n → Int :=
  fun a => entryContent T a

/-- Lemma 5.7 basis-level vocabulary: content sequence of a standard tableau. -/
noncomputable def S05_Lem5_07_tableauContentSequence {n : Nat}
    {lam : YoungDiagram n} (T : StandardYoungTableau lam) : Fin n → Int :=
  tableauContentSequence T

/-- Lower removable corners have strictly smaller content than higher removable
corners. -/
theorem removableCornerBox_content_lt_of_row_lt {n : Nat}
    {lam : YoungDiagram n} {u v : YoungCell lam}
    (hu : IsRemovableCornerBox lam (YoungCell.toNatPair u))
    (hv : IsRemovableCornerBox lam (YoungCell.toNatPair v))
    (hrow : YoungCell.row u < YoungCell.row v) :
    YoungCell.content v < YoungCell.content u := by
  rcases hu with ⟨_hu_box, hu_last, hu_below⟩
  rcases hv with ⟨_hv_box, hv_last, _hv_below⟩
  have hu_below' :
      youngRow lam (YoungCell.row u + 1) <= YoungCell.col u := by
    simpa [YoungCell.toNatPair] using hu_below
  have hv_last' :
      YoungCell.col v + 1 = youngRow lam (YoungCell.row v) := by
    simpa [YoungCell.toNatPair] using hv_last
  unfold YoungCell.content
  have hmono :
      youngRow lam (YoungCell.row v) <=
        youngRow lam (YoungCell.row u + 1) :=
    youngRow_le_of_le lam (by omega)
  have hv_col_lt_row_v : YoungCell.col v < youngRow lam (YoungCell.row v) := by
    omega
  have hv_col_lt_succ :
      YoungCell.col v < youngRow lam (YoungCell.row u + 1) := by
    exact lt_of_lt_of_le hv_col_lt_row_v hmono
  have hv_col_lt_u_col : YoungCell.col v < YoungCell.col u := by
    exact lt_of_lt_of_le hv_col_lt_succ hu_below'
  omega

/-- Removable corner boxes in a fixed Young diagram have distinct contents. -/
theorem removableCornerBox_eq_of_content_eq {n : Nat}
    {lam : YoungDiagram n} {u v : YoungCell lam}
    (hu : IsRemovableCornerBox lam (YoungCell.toNatPair u))
    (hv : IsRemovableCornerBox lam (YoungCell.toNatPair v))
    (hcontent : YoungCell.content u = YoungCell.content v) :
    u = v := by
  rcases lt_trichotomy (YoungCell.row u) (YoungCell.row v) with hlt | heq | hgt
  · have hlt_content := removableCornerBox_content_lt_of_row_lt hu hv hlt
    omega
  · rcases hu with ⟨_hu_box, hu_last, _hu_below⟩
    rcases hv with ⟨_hv_box, hv_last, _hv_below⟩
    apply YoungCell.ext_row_col heq
    unfold YoungCell.content at hcontent
    omega
  · have hlt_content := removableCornerBox_content_lt_of_row_lt hv hu hgt
    omega

/-- If two maximum-entry cells have the same content, then they are the same
cell. -/
theorem tableauMaxAt_eq_of_entryContent_eq {n : Nat}
    {lam : YoungDiagram (n + 1)}
    {T U : StandardYoungTableau lam} {u v : YoungCell lam}
    (hu : TableauMaxAt T u) (hv : TableauMaxAt U v)
    (hcontent :
      entryContent T (Fin.last n) = entryContent U (Fin.last n)) :
    u = v := by
  have hcell_u : cellOfEntry T (Fin.last n) = u :=
    cellOfEntry_eq_of_entry T hu
  have hcell_v : cellOfEntry U (Fin.last n) = v :=
    cellOfEntry_eq_of_entry U hv
  have hcontent_cells : YoungCell.content u = YoungCell.content v := by
    rw [← hcell_u, ← hcell_v]
    simpa [entryContent] using hcontent
  exact removableCornerBox_eq_of_content_eq
    (removableCornerBox_of_tableauMaxAt T hu)
    (removableCornerBox_of_tableauMaxAt U hv)
    hcontent_cells

/-- The deleted-corner cell is independent of proof choices for the same
one-box child and same changed row. -/
theorem deletedCornerCellOfOneBoxChildRow_eq_of_same_row_form
    {n : Nat} {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n}
    (h h' : IsOneBoxChild lam mu) {r : Nat}
    (hr hr' :
      youngRow lam r = youngRow mu r + 1 ∧
      ∀ t : Nat, t ≠ r → youngRow lam t = youngRow mu t) :
    deletedCornerCellOfOneBoxChildRow h hr =
      deletedCornerCellOfOneBoxChildRow h' hr' := by
  apply YoungCell.ext_row_col
  · rfl
  · rfl

/-- The content sequence of a standard tableau determines the tableau. -/
theorem tableauContentSequence_injective {n : Nat} {lam : YoungDiagram n}
    {T U : StandardYoungTableau lam}
    (h : tableauContentSequence T = tableauContentSequence U) :
    T = U := by
  induction n with
  | zero =>
      apply standardYoungTableau_ext_entry
      intro u
      exact Fin.elim0 u.1.1
  | succ n ih =>
      let r : RemovableRow lam := maxRemovableRow T
      let hchild : IsOneBoxChild lam (removableRowToOneBoxChild lam r) :=
        removableRowToOneBoxChild_isOneBoxChild lam r
      let hr :
          youngRow lam r.1 =
              youngRow (removableRowToOneBoxChild lam r) r.1 + 1 ∧
            ∀ s : Nat, s ≠ r.1 →
              youngRow lam s = youngRow (removableRowToOneBoxChild lam r) s :=
        row_form_deleteRemovableRowDiagram lam r.2
      let u := deletedCornerCellOfOneBoxChildRow hchild hr
      have hu_eq_canonical :
          u =
            deletedCornerCellOfOneBoxChildRow
              (removableRowToOneBoxChild_isOneBoxChild lam (maxRemovableRow T))
              (row_form_deleteRemovableRowDiagram lam (maxRemovableRow T).2) := by
        change u =
          deletedCornerCellOfOneBoxChildRow
            (removableRowToOneBoxChild_isOneBoxChild lam r)
            (row_form_deleteRemovableRowDiagram lam r.2)
        exact deletedCornerCellOfOneBoxChildRow_eq_of_same_row_form
          hchild (removableRowToOneBoxChild_isOneBoxChild lam r)
          hr (row_form_deleteRemovableRowDiagram lam r.2)
      have huT : TableauMaxAt T u := by
        rw [hu_eq_canonical]
        exact tableauMaxAt_deletedCorner_maxRemovableRow T
      have hlast :
          entryContent T (Fin.last n) = entryContent U (Fin.last n) := by
        have hfun := congrFun h (Fin.last n)
        simpa [tableauContentSequence] using hfun
      have hmax_eq :
          maxRemovableCornerCell T = maxRemovableCornerCell U := by
        exact tableauMaxAt_eq_of_entryContent_eq
          (tableauMaxAt_maxRemovableCornerCell T)
          (tableauMaxAt_maxRemovableCornerCell U)
          hlast
      have hu_corner : IsRemovableCornerBox lam (YoungCell.toNatPair u) := by
        rw [hu_eq_canonical]
        exact deletedCornerCell_removableCornerBox_of_removableRow
          (maxRemovableRow T)
      have hu_eq_maxT : u = maxRemovableCornerCell T := by
        rcases existsUnique_removableCornerBox_tableauMaxAt T with
          ⟨w, hw, huniq⟩
        have hu_eq_w : u = w := huniq u ⟨huT, hu_corner⟩
        have hmax_eq_w :
            maxRemovableCornerCell T = w :=
          huniq (maxRemovableCornerCell T) (maxRemovableCornerCell_spec T)
        exact hu_eq_w.trans hmax_eq_w.symm
      have huU : TableauMaxAt U u := by
        rw [hu_eq_maxT, hmax_eq]
        exact tableauMaxAt_maxRemovableCornerCell U
      let DT : StandardYoungTableau (removableRowToOneBoxChild lam r) :=
        deleteMaxAsStandardYoungTableauOfOneBoxChildRow
          hchild hr u (deletedCornerCell_row hchild hr)
          (deletedCornerCell_col hchild hr) T huT
      let DU : StandardYoungTableau (removableRowToOneBoxChild lam r) :=
        deleteMaxAsStandardYoungTableauOfOneBoxChildRow
          hchild hr u (deletedCornerCell_row hchild hr)
          (deletedCornerCell_col hchild hr) U huU
      have hdelete_seq : tableauContentSequence DT = tableauContentSequence DU := by
        funext a
        have hTdel :
            entryContent DT a = entryContent T (Fin.castSucc a) := by
          simpa [DT] using
            deleteMax_entryContent hchild hr u
              (deletedCornerCell_row hchild hr)
              (deletedCornerCell_col hchild hr) T huT a
        have hUdel :
            entryContent DU a = entryContent U (Fin.castSucc a) := by
          simpa [DU] using
            deleteMax_entryContent hchild hr u
              (deletedCornerCell_row hchild hr)
              (deletedCornerCell_col hchild hr) U huU a
        have hparent := congrFun h (Fin.castSucc a)
        calc
          tableauContentSequence DT a = entryContent DT a := rfl
          _ = entryContent T (Fin.castSucc a) := hTdel
          _ = entryContent U (Fin.castSucc a) := by
              simpa [tableauContentSequence] using hparent
          _ = entryContent DU a := hUdel.symm
          _ = tableauContentSequence DU a := rfl
      have hDU : DT = DU := ih hdelete_seq
      calc
        T =
            insertMaxAsStandardYoungTableauOfOneBoxChildRow hchild hr DT := by
              simpa [DT] using
                (insertMax_deleteMaxAsStandardYoungTableauOfOneBoxChildRow
                  hchild hr T huT).symm
        _ =
            insertMaxAsStandardYoungTableauOfOneBoxChildRow hchild hr DU := by
              rw [hDU]
        _ = U := by
              simpa [DU] using
                insertMax_deleteMaxAsStandardYoungTableauOfOneBoxChildRow
                  hchild hr U huU

/-- Lemma 5.7 paper-facing injectivity component: the entry-content sequence
determines a standard tableau. -/
theorem S05_Lem5_07_tableauContentSequence_injective {n : Nat}
    {lam : YoungDiagram n} {T U : StandardYoungTableau lam}
    (h : tableauContentSequence T = tableauContentSequence U) :
    T = U := by
  exact tableauContentSequence_injective h

/-- Distinct standard tableaux differ in at least one entry content. -/
theorem exists_entryContent_ne_of_ne {n : Nat} {lam : YoungDiagram n}
    {T U : StandardYoungTableau lam} (hneq : U ≠ T) :
    ∃ a : Fin n, entryContent U a ≠ entryContent T a := by
  by_contra hnone
  have hseq : tableauContentSequence U = tableauContentSequence T := by
    funext a
    by_contra hne
    exact hnone ⟨a, by simpa [tableauContentSequence] using hne⟩
  exact hneq (tableauContentSequence_injective hseq)

/-- Lemma 5.7 paper-facing separation component: distinct tableaux differ in
some diagonal-content eigenvalue. -/
theorem S05_Lem5_07_diagonalContent_commonEigen_support {n : Nat}
    {lam : YoungDiagram n} {T U : StandardYoungTableau lam} (hneq : U ≠ T) :
    ∃ a : Fin n, entryContent U a ≠ entryContent T a := by
  exact exists_entryContent_ne_of_ne hneq

/-- Basis-level component: after swapping adjacent values, the lower entry gets
the old upper entry's content. -/
theorem tableauContentSequence_adjacentSwap_lo {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne :
      YoungCell.row (adjacentLoCell T a) ≠
        YoungCell.row (adjacentHiCell T a))
    (hcol_ne :
      YoungCell.col (adjacentLoCell T a) ≠
        YoungCell.col (adjacentHiCell T a)) :
    tableauContentSequence (adjacentSwapTableau T a hrow_ne hcol_ne)
        (adjacentEntryLo a) =
      tableauContentSequence T (adjacentEntryHi a) := by
  exact adjacentSwapTableau_entryContent_lo T a hrow_ne hcol_ne

/-- Basis-level component: after swapping adjacent values, the upper entry gets
the old lower entry's content. -/
theorem tableauContentSequence_adjacentSwap_hi {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne :
      YoungCell.row (adjacentLoCell T a) ≠
        YoungCell.row (adjacentHiCell T a))
    (hcol_ne :
      YoungCell.col (adjacentLoCell T a) ≠
        YoungCell.col (adjacentHiCell T a)) :
    tableauContentSequence (adjacentSwapTableau T a hrow_ne hcol_ne)
        (adjacentEntryHi a) =
      tableauContentSequence T (adjacentEntryLo a) := by
  exact adjacentSwapTableau_entryContent_hi T a hrow_ne hcol_ne

/-- Basis-level component: adjacent swaps preserve all non-adjacent content
values. -/
theorem tableauContentSequence_adjacentSwap_of_ne_lo_hi {n : Nat}
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
    tableauContentSequence (adjacentSwapTableau T a hrow_ne hcol_ne) b =
      tableauContentSequence T b := by
  exact adjacentSwapTableau_entryContent_of_ne_lo_hi T a hrow_ne hcol_ne hblo hbhi

/-- Lemma 5.7 basis-level component: after swapping adjacent values, the lower
entry gets the old upper entry's content. -/
theorem S05_Lem5_07_tableauContentSequence_adjacentSwap_lo {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne :
      YoungCell.row (adjacentLoCell T a) ≠
        YoungCell.row (adjacentHiCell T a))
    (hcol_ne :
      YoungCell.col (adjacentLoCell T a) ≠
        YoungCell.col (adjacentHiCell T a)) :
    tableauContentSequence (adjacentSwapTableau T a hrow_ne hcol_ne)
        (adjacentEntryLo a) =
      tableauContentSequence T (adjacentEntryHi a) := by
  exact tableauContentSequence_adjacentSwap_lo T a hrow_ne hcol_ne

/-- Lemma 5.7 basis-level component: after swapping adjacent values, the upper
entry gets the old lower entry's content. -/
theorem S05_Lem5_07_tableauContentSequence_adjacentSwap_hi {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne :
      YoungCell.row (adjacentLoCell T a) ≠
        YoungCell.row (adjacentHiCell T a))
    (hcol_ne :
      YoungCell.col (adjacentLoCell T a) ≠
        YoungCell.col (adjacentHiCell T a)) :
    tableauContentSequence (adjacentSwapTableau T a hrow_ne hcol_ne)
        (adjacentEntryHi a) =
      tableauContentSequence T (adjacentEntryLo a) := by
  exact tableauContentSequence_adjacentSwap_hi T a hrow_ne hcol_ne

/-- Lemma 5.7 basis-level component: adjacent swaps preserve non-adjacent
content-sequence values. -/
theorem S05_Lem5_07_tableauContentSequence_adjacentSwap_of_ne_lo_hi {n : Nat}
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
    tableauContentSequence (adjacentSwapTableau T a hrow_ne hcol_ne) b =
      tableauContentSequence T b := by
  exact tableauContentSequence_adjacentSwap_of_ne_lo_hi T a hrow_ne hcol_ne hblo hbhi

/-- Lemma 5.7 basis-level component: adjacent entry contents differ by `+1`
in the same-row case. -/
theorem S05_Lem5_07_entryContent_adjacent_hi_eq_lo_add_one_of_sameRow
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow :
      YoungCell.row (adjacentLoCell T a) =
        YoungCell.row (adjacentHiCell T a)) :
    entryContent T (adjacentEntryHi a) =
      entryContent T (adjacentEntryLo a) + 1 := by
  simpa [entryContent, adjacentHiCell, adjacentLoCell]
    using adjacent_content_hi_eq_lo_add_one_of_sameRow T a hrow

/-- Lemma 5.7 basis-level component: symmetric form of the same-row adjacent
content difference. -/
theorem S05_Lem5_07_entryContent_adjacent_lo_eq_hi_sub_one_of_sameRow
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow :
      YoungCell.row (adjacentLoCell T a) =
        YoungCell.row (adjacentHiCell T a)) :
    entryContent T (adjacentEntryLo a) =
      entryContent T (adjacentEntryHi a) - 1 := by
  have h :=
    S05_Lem5_07_entryContent_adjacent_hi_eq_lo_add_one_of_sameRow T a hrow
  omega

/-- Lemma 5.7 basis-level component: adjacent entry contents differ by `-1`
in the same-column case. -/
theorem S05_Lem5_07_entryContent_adjacent_hi_eq_lo_sub_one_of_sameCol
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol :
      YoungCell.col (adjacentLoCell T a) =
        YoungCell.col (adjacentHiCell T a)) :
    entryContent T (adjacentEntryHi a) =
      entryContent T (adjacentEntryLo a) - 1 := by
  simpa [entryContent, adjacentHiCell, adjacentLoCell]
    using adjacent_content_hi_eq_lo_sub_one_of_sameCol T a hcol

/-- Lemma 5.7 basis-level component: symmetric form of the same-column adjacent
content difference. -/
theorem S05_Lem5_07_entryContent_adjacent_lo_eq_hi_add_one_of_sameCol
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol :
      YoungCell.col (adjacentLoCell T a) =
        YoungCell.col (adjacentHiCell T a)) :
    entryContent T (adjacentEntryLo a) =
      entryContent T (adjacentEntryHi a) + 1 := by
  have h :=
    S05_Lem5_07_entryContent_adjacent_hi_eq_lo_sub_one_of_sameCol T a hcol
  omega

/-- Lemma 5.7 coordinate component: the diagonal content operator has
eigenvalue equal to the entry content on the matching tableau basis vector. -/
theorem S05_Lem5_07_jucysMurphyDiagonalOperator_basis_self
    {n : Nat} {lam : YoungDiagram n}
    (T : StandardYoungTableau lam) (a : Fin n) :
    jucysMurphyDiagonalOperator a (tableauBasisVec T) T =
      (entryContent T a : ℝ) := by
  exact jucysMurphyDiagonalOperator_basis_self T a

/-- Lemma 5.7 coordinate component: the diagonal content operator has zero
coordinate on every other tableau basis vector. -/
theorem S05_Lem5_07_jucysMurphyDiagonalOperator_basis_ne
    {n : Nat} {lam : YoungDiagram n}
    {S T : StandardYoungTableau lam} (a : Fin n)
    (hST : S ≠ T) :
    jucysMurphyDiagonalOperator a (tableauBasisVec T) S = 0 := by
  exact jucysMurphyDiagonalOperator_basis_ne a hST

/-- Lemma 5.7 coordinate component: each tableau basis vector is an eigenvector
of the diagonal content operator. -/
theorem S05_Lem5_07_jucysMurphyDiagonalOperator_basis_eigen
    {n : Nat} {lam : YoungDiagram n}
    (T : StandardYoungTableau lam) (a : Fin n) :
    jucysMurphyDiagonalOperator a (tableauBasisVec T) =
      fun S => (entryContent T a : ℝ) * tableauBasisVec T S := by
  exact jucysMurphyDiagonalOperator_basis_eigen T a

/-- If a vector has `T`'s diagonal-content eigenvalue at coordinate `a`, then
any tableau whose `a`-content differs from `T` has zero coefficient. -/
theorem diagonalContent_eigen_coordinate_zero_of_content_ne {n : Nat}
    {lam : YoungDiagram n} {T U : StandardYoungTableau lam}
    {f : TableauSpace lam} {a : Fin n}
    (hf :
      jucysMurphyDiagonalOperator a f =
        fun S => (entryContent T a : ℝ) * f S)
    (hcontent : entryContent U a ≠ entryContent T a) :
    f U = 0 := by
  have hcoord := congrFun hf U
  change (entryContent U a : ℝ) * f U =
    (entryContent T a : ℝ) * f U at hcoord
  have hsub :
      ((entryContent U a : ℝ) - (entryContent T a : ℝ)) * f U = 0 := by
    nlinarith
  have hcoeff_ne :
      ((entryContent U a : ℝ) - (entryContent T a : ℝ)) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast hcontent
  rcases mul_eq_zero.mp hsub with hzero | hfzero
  · exact False.elim (hcoeff_ne hzero)
  · exact hfzero

/-- A simultaneous eigenvector for all explicit diagonal content operators is
supported on the unique tableau with that content sequence. -/
theorem diagonalContent_commonEigenvector_eq_smul_basis {n : Nat}
    {lam : YoungDiagram n} (T : StandardYoungTableau lam)
    (f : TableauSpace lam)
    (hf :
      ∀ a : Fin n,
        jucysMurphyDiagonalOperator a f =
          fun U => (entryContent T a : ℝ) * f U) :
    f = fun U => f T * tableauBasisVec T U := by
  funext U
  by_cases hUT : U = T
  · subst U
    simp [tableauBasisVec]
  · rcases exists_entryContent_ne_of_ne hUT with ⟨a, hcontent⟩
    have hzero : f U = 0 :=
      diagonalContent_eigen_coordinate_zero_of_content_ne (hf a) hcontent
    rw [hzero]
    simp [tableauBasisVec, hUT]

/-- Paper lemma `lem:jucys-murphy-eigenbasis`, rewritten Section 5 form: the
explicit diagonal content operators have one-dimensional common eigenspaces in
the tableau coordinate basis.  Appendix A.2 supplies the external
Jucys--Murphy group-algebra identification. -/
theorem S05_Lem5_07_diagonalContentEigenspaces {n : Nat}
    {lam : YoungDiagram n} (T : StandardYoungTableau lam)
    (f : TableauSpace lam)
    (hf :
      ∀ a : Fin n,
        jucysMurphyDiagonalOperator a f =
          fun U => (entryContent T a : ℝ) * f U) :
    f = fun U => f T * tableauBasisVec T U := by
  exact diagonalContent_commonEigenvector_eq_smul_basis T f hf

end DictatorshipTesting
