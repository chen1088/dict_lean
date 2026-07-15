import DictatorshipTesting.Paper.S05_Lem5_01_AdjacentTranspositionsInYoungsBasis
import DictatorshipTesting.Paper.S05_Thm5_03_JucysMurphyContentAction
import AlgebraicLibrary.Young.OrthogonalRepresentation
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.FinRange
import AlgebraicLibrary.Young.StandardTableau
import AlgebraicLibrary.Order.LinearExtension

open AlgebraicLibrary

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Int_OneBoxDeletionIntertwining`
- `DictatorshipTesting.Paper.S05_Int_RegularYoungBlockDecomposition`
- `DictatorshipTesting.Paper.S05_Lem5_05_YoungBasisScalarCommutant`
-/

/-!
# Lemma 5.4: Content separation and tableau connectivity

The content-separation argument and the adjacent-swap connectivity proof are
both contained in this paper-facing module.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.4 basis-level vocabulary: content of a tableau cell. -/
def S05_Lem5_04_cellContent {n : Nat} {lam : YoungDiagram n}
    (u : YoungCell lam) : Int :=
  YoungCell.content u

/-- Lemma 5.4 basis-level vocabulary: content of the cell containing an entry. -/
noncomputable def S05_Lem5_04_entryContent {n : Nat} {lam : YoungDiagram n}
    (T : StandardYoungTableau lam) (a : Fin n) : Int :=
  entryContent T a

/-- Basis-level content sequence of a standard tableau, indexed by entries. -/
noncomputable def tableauContentSequence {n : Nat} {lam : YoungDiagram n}
    (T : StandardYoungTableau lam) : Fin n → Int :=
  fun a => entryContent T a

/-- Lemma 5.4 basis-level vocabulary: content sequence of a standard tableau. -/
noncomputable def S05_Lem5_04_tableauContentSequence {n : Nat}
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

/-- The content of a deleted corner is the child row length minus its row
index. -/
theorem deletedCornerCell_content
    {n : Nat} {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      ∀ t : Nat, t ≠ r → youngRow lam t = youngRow mu t) :
    YoungCell.content (deletedCornerCellOfOneBoxChildRow h hr) =
      (youngRow mu r : Int) - (r : Int) := by
  unfold YoungCell.content
  rw [deletedCornerCell_col, deletedCornerCell_row]

/-- For a fixed child diagram, the possible added-corner contents strictly
distinguish their row indices. -/
theorem childRow_sub_row_injective {n : Nat} (mu : YoungDiagram n)
    {r s : Nat}
    (h : (youngRow mu r : Int) - (r : Int) =
      (youngRow mu s : Int) - (s : Int)) :
    r = s := by
  rcases lt_trichotomy r s with hrs | hrs | hrs
  · have hrow : youngRow mu s ≤ youngRow mu r :=
      youngRow_le_of_le mu (Nat.le_of_lt hrs)
    have hrowInt : (youngRow mu s : Int) ≤ (youngRow mu r : Int) := by
      exact_mod_cast hrow
    omega
  · exact hrs
  · have hrow : youngRow mu r ≤ youngRow mu s :=
      youngRow_le_of_le mu (Nat.le_of_lt hrs)
    have hrowInt : (youngRow mu r : Int) ≤ (youngRow mu s : Int) := by
      exact_mod_cast hrow
    omega

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

/-- The full entry-content sequence determines not only a tableau inside a
fixed shape, but also the shape itself. -/
theorem tableauContentSequence_determines_shape
    {n : Nat} {lam mu : YoungDiagram n}
    (T : StandardYoungTableau lam) (U : StandardYoungTableau mu)
    (h : tableauContentSequence T = tableauContentSequence U) :
    lam = mu := by
  induction n with
  | zero =>
      apply youngDiagram_ext_youngRow
      intro i
      simp [youngRow]
  | succ n ih =>
      let rT : RemovableRow lam := maxRemovableRow T
      let childT : YoungDiagram n := removableRowToOneBoxChild lam rT
      let hchildT : IsOneBoxChild lam childT :=
        removableRowToOneBoxChild_isOneBoxChild lam rT
      let hrT :
          youngRow lam rT.1 = youngRow childT rT.1 + 1 ∧
            ∀ s : Nat, s ≠ rT.1 →
              youngRow lam s = youngRow childT s :=
        row_form_deleteRemovableRowDiagram lam rT.2
      let uT : YoungCell lam :=
        deletedCornerCellOfOneBoxChildRow hchildT hrT
      have huT : TableauMaxAt T uT := by
        change TableauMaxAt T
          (deletedCornerCellOfOneBoxChildRow
            (removableRowToOneBoxChild_isOneBoxChild lam (maxRemovableRow T))
            (row_form_deleteRemovableRowDiagram lam (maxRemovableRow T).2))
        exact tableauMaxAt_deletedCorner_maxRemovableRow T
      let DT : StandardYoungTableau childT :=
        deleteMaxAsStandardYoungTableauOfOneBoxChildRow
          hchildT hrT uT (deletedCornerCell_row hchildT hrT)
          (deletedCornerCell_col hchildT hrT) T huT

      let rU : RemovableRow mu := maxRemovableRow U
      let childU : YoungDiagram n := removableRowToOneBoxChild mu rU
      let hchildU : IsOneBoxChild mu childU :=
        removableRowToOneBoxChild_isOneBoxChild mu rU
      let hrU :
          youngRow mu rU.1 = youngRow childU rU.1 + 1 ∧
            ∀ s : Nat, s ≠ rU.1 →
              youngRow mu s = youngRow childU s :=
        row_form_deleteRemovableRowDiagram mu rU.2
      let uU : YoungCell mu :=
        deletedCornerCellOfOneBoxChildRow hchildU hrU
      have huU : TableauMaxAt U uU := by
        change TableauMaxAt U
          (deletedCornerCellOfOneBoxChildRow
            (removableRowToOneBoxChild_isOneBoxChild mu (maxRemovableRow U))
            (row_form_deleteRemovableRowDiagram mu (maxRemovableRow U).2))
        exact tableauMaxAt_deletedCorner_maxRemovableRow U
      let DU : StandardYoungTableau childU :=
        deleteMaxAsStandardYoungTableauOfOneBoxChildRow
          hchildU hrU uU (deletedCornerCell_row hchildU hrU)
          (deletedCornerCell_col hchildU hrU) U huU

      have hdelete_seq :
          tableauContentSequence DT = tableauContentSequence DU := by
        funext a
        have hTdel :
            entryContent DT a = entryContent T (Fin.castSucc a) := by
          simpa [DT] using
            deleteMax_entryContent hchildT hrT uT
              (deletedCornerCell_row hchildT hrT)
              (deletedCornerCell_col hchildT hrT) T huT a
        have hUdel :
            entryContent DU a = entryContent U (Fin.castSucc a) := by
          simpa [DU] using
            deleteMax_entryContent hchildU hrU uU
              (deletedCornerCell_row hchildU hrU)
              (deletedCornerCell_col hchildU hrU) U huU a
        have hparent := congrFun h (Fin.castSucc a)
        calc
          tableauContentSequence DT a = entryContent DT a := rfl
          _ = entryContent T (Fin.castSucc a) := hTdel
          _ = entryContent U (Fin.castSucc a) := by
            simpa [tableauContentSequence] using hparent
          _ = entryContent DU a := hUdel.symm
          _ = tableauContentSequence DU a := rfl
      have hchildren : childT = childU := ih DT DU hdelete_seq
      have hlast :
          entryContent T (Fin.last n) = entryContent U (Fin.last n) := by
        have hfun := congrFun h (Fin.last n)
        simpa [tableauContentSequence] using hfun
      have hcellT : cellOfEntry T (Fin.last n) = uT :=
        cellOfEntry_eq_of_entry T huT
      have hcellU : cellOfEntry U (Fin.last n) = uU :=
        cellOfEntry_eq_of_entry U huU
      have hcornerContent : YoungCell.content uT = YoungCell.content uU := by
        simpa [entryContent, hcellT, hcellU] using hlast
      have hrowContent :
          (youngRow childT rT.1 : Int) - (rT.1 : Int) =
            (youngRow childU rU.1 : Int) - (rU.1 : Int) := by
        calc
          (youngRow childT rT.1 : Int) - (rT.1 : Int) =
              YoungCell.content uT :=
            (deletedCornerCell_content hchildT hrT).symm
          _ = YoungCell.content uU := hcornerContent
          _ = (youngRow childU rU.1 : Int) - (rU.1 : Int) :=
            deletedCornerCell_content hchildU hrU
      rw [hchildren] at hrowContent
      have hrows : rT.1 = rU.1 :=
        childRow_sub_row_injective childU hrowContent
      apply youngDiagram_ext_youngRow
      intro i
      by_cases hi : i = rT.1
      · calc
          youngRow lam i = youngRow childT rT.1 + 1 := by
            rw [hi, hrT.1]
          _ = youngRow childU rU.1 + 1 := by
            rw [hchildren, hrows]
          _ = youngRow mu i := by
            rw [hi, hrows, hrU.1]
      · have hiU : i ≠ rU.1 := by
          intro hi'
          apply hi
          rw [hi', ← hrows]
        calc
          youngRow lam i = youngRow childT i := hrT.2 i hi
          _ = youngRow childU i := by rw [hchildren]
          _ = youngRow mu i := (hrU.2 i hiU).symm

/-- Lemma 5.4 paper-facing injectivity component: the entry-content sequence
determines a standard tableau. -/
theorem S05_Lem5_04_tableauContentSequence_injective {n : Nat}
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

/-- Lemma 5.4 paper-facing separation component: distinct tableaux differ in
some diagonal-content eigenvalue. -/
theorem S05_Lem5_04_diagonalContent_commonEigen_support {n : Nat}
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

/-- Lemma 5.4 basis-level component: after swapping adjacent values, the lower
entry gets the old upper entry's content. -/
theorem S05_Lem5_04_tableauContentSequence_adjacentSwap_lo {n : Nat}
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

/-- Lemma 5.4 basis-level component: after swapping adjacent values, the upper
entry gets the old lower entry's content. -/
theorem S05_Lem5_04_tableauContentSequence_adjacentSwap_hi {n : Nat}
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

/-- Lemma 5.4 basis-level component: adjacent swaps preserve non-adjacent
content-sequence values. -/
theorem S05_Lem5_04_tableauContentSequence_adjacentSwap_of_ne_lo_hi {n : Nat}
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

/-- Lemma 5.4 basis-level component: adjacent entry contents differ by `+1`
in the same-row case. -/
theorem S05_Lem5_04_entryContent_adjacent_hi_eq_lo_add_one_of_sameRow
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow :
      YoungCell.row (adjacentLoCell T a) =
        YoungCell.row (adjacentHiCell T a)) :
    entryContent T (adjacentEntryHi a) =
      entryContent T (adjacentEntryLo a) + 1 := by
  simpa [entryContent, adjacentHiCell, adjacentLoCell]
    using adjacent_content_hi_eq_lo_add_one_of_sameRow T a hrow

/-- Lemma 5.4 basis-level component: symmetric form of the same-row adjacent
content difference. -/
theorem S05_Lem5_04_entryContent_adjacent_lo_eq_hi_sub_one_of_sameRow
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow :
      YoungCell.row (adjacentLoCell T a) =
        YoungCell.row (adjacentHiCell T a)) :
    entryContent T (adjacentEntryLo a) =
      entryContent T (adjacentEntryHi a) - 1 := by
  have h :=
    S05_Lem5_04_entryContent_adjacent_hi_eq_lo_add_one_of_sameRow T a hrow
  omega

/-- Lemma 5.4 basis-level component: adjacent entry contents differ by `-1`
in the same-column case. -/
theorem S05_Lem5_04_entryContent_adjacent_hi_eq_lo_sub_one_of_sameCol
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol :
      YoungCell.col (adjacentLoCell T a) =
        YoungCell.col (adjacentHiCell T a)) :
    entryContent T (adjacentEntryHi a) =
      entryContent T (adjacentEntryLo a) - 1 := by
  simpa [entryContent, adjacentHiCell, adjacentLoCell]
    using adjacent_content_hi_eq_lo_sub_one_of_sameCol T a hcol

/-- Lemma 5.4 basis-level component: symmetric form of the same-column adjacent
content difference. -/
theorem S05_Lem5_04_entryContent_adjacent_lo_eq_hi_add_one_of_sameCol
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol :
      YoungCell.col (adjacentLoCell T a) =
        YoungCell.col (adjacentHiCell T a)) :
    entryContent T (adjacentEntryLo a) =
      entryContent T (adjacentEntryHi a) + 1 := by
  have h :=
    S05_Lem5_04_entryContent_adjacent_hi_eq_lo_sub_one_of_sameCol T a hcol
  omega

/-- Lemma 5.4 coordinate component: the diagonal content operator has
eigenvalue equal to the entry content on the matching tableau basis vector. -/
theorem S05_Lem5_04_jucysMurphyDiagonalOperator_basis_self
    {n : Nat} {lam : YoungDiagram n}
    (T : StandardYoungTableau lam) (a : Fin n) :
    jucysMurphyDiagonalOperator a (tableauBasisVec T) T =
      (entryContent T a : ℝ) := by
  exact jucysMurphyDiagonalOperator_basis_self T a

/-- Lemma 5.4 coordinate component: the diagonal content operator has zero
coordinate on every other tableau basis vector. -/
theorem S05_Lem5_04_jucysMurphyDiagonalOperator_basis_ne
    {n : Nat} {lam : YoungDiagram n}
    {S T : StandardYoungTableau lam} (a : Fin n)
    (hST : S ≠ T) :
    jucysMurphyDiagonalOperator a (tableauBasisVec T) S = 0 := by
  exact jucysMurphyDiagonalOperator_basis_ne a hST

/-- Lemma 5.4 coordinate component: each tableau basis vector is an eigenvector
of the diagonal content operator. -/
theorem S05_Lem5_04_jucysMurphyDiagonalOperator_basis_eigen
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
the tableau coordinate basis.  Section 5.2 supplies the external
Jucys--Murphy group-algebra identification. -/
theorem S05_Lem5_04_diagonalContentEigenspaces {n : Nat}
    {lam : YoungDiagram n} (T : StandardYoungTableau lam)
    (f : TableauSpace lam)
    (hf :
      ∀ a : Fin n,
        jucysMurphyDiagonalOperator a f =
          fun U => (entryContent T a : ℝ) * f U) :
    f = fun U => f T * tableauBasisVec T U := by
  exact diagonalContent_commonEigenvector_eq_smul_basis T f hf

/-- The strict row-or-column order on boxes of a Young diagram. Standardness
of a tableau is exactly strict increase along these comparisons. -/
def YoungCellRowColumnLt {n : Nat} {lam : YoungDiagram n}
    (u v : YoungCell lam) : Prop :=
  (YoungCell.row u = YoungCell.row v ∧ YoungCell.col u < YoungCell.col v) ∨
    (YoungCell.col u = YoungCell.col v ∧ YoungCell.row u < YoungCell.row v)

/-- The boxes of a standard tableau, listed in increasing order of their
entries. -/
noncomputable def standardTableauBoxOrder {n : Nat} {lam : YoungDiagram n}
    (T : StandardYoungTableau lam) : List (YoungCell lam) :=
  List.ofFn (cellOfEntry T)

@[simp] theorem standardTableauBoxOrder_length
    {n : Nat} {lam : YoungDiagram n} (T : StandardYoungTableau lam) :
    (standardTableauBoxOrder T).length = n := by
  simp [standardTableauBoxOrder]

theorem cellOfEntry_injective {n : Nat} {lam : YoungDiagram n}
    (T : StandardYoungTableau lam) : Function.Injective (cellOfEntry T) := by
  intro a b hab
  have hentry := congrArg T.entry hab
  simpa only [entry_cellOfEntry] using hentry

theorem standardTableauBoxOrder_nodup
    {n : Nat} {lam : YoungDiagram n} (T : StandardYoungTableau lam) :
    (standardTableauBoxOrder T).Nodup := by
  rw [standardTableauBoxOrder, List.nodup_ofFn]
  exact cellOfEntry_injective T

/-- The box-order list of a standard tableau is a linear extension of the
strict row-or-column order. -/
theorem standardTableauBoxOrder_isLinearExtension
    {n : Nat} {lam : YoungDiagram n} (T : StandardYoungTableau lam) :
    IsLinearExtension YoungCellRowColumnLt (standardTableauBoxOrder T) := by
  refine ⟨standardTableauBoxOrder_nodup T, ?_⟩
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [standardTableauBoxOrder_length] at hi hj
  simp only [standardTableauBoxOrder, List.getElem_ofFn]
  intro hrel
  rcases hrel with hrow | hcol
  · have hlt := T.row_strict hrow.1 hrow.2
    rw [entry_cellOfEntry, entry_cellOfEntry] at hlt
    have hji : j < i := by simpa using hlt
    omega
  · have hlt := T.col_strict hcol.1 hcol.2
    rw [entry_cellOfEntry, entry_cellOfEntry] at hlt
    have hji : j < i := by simpa using hlt
    omega

/-- Every box occurs in the box-order list. -/
theorem mem_standardTableauBoxOrder
    {n : Nat} {lam : YoungDiagram n} (T : StandardYoungTableau lam)
    (u : YoungCell lam) :
    u ∈ standardTableauBoxOrder T := by
  rw [standardTableauBoxOrder, List.mem_ofFn']
  refine ⟨T.entry u, ?_⟩
  exact cellOfEntry_eq_of_entry T rfl

/-- Box-order lists of two tableaux of the same shape list the same boxes with
multiplicity one. -/
theorem standardTableauBoxOrder_perm
    {n : Nat} {lam : YoungDiagram n} (T U : StandardYoungTableau lam) :
    (standardTableauBoxOrder T).Perm (standardTableauBoxOrder U) := by
  apply (List.perm_ext_iff_of_nodup
    (standardTableauBoxOrder_nodup T)
    (standardTableauBoxOrder_nodup U)).2
  intro u
  simp only [mem_standardTableauBoxOrder]

/-- A tableau is determined by its increasing box-order list. -/
theorem standardTableauBoxOrder_injective
    {n : Nat} {lam : YoungDiagram n} {T U : StandardYoungTableau lam}
    (horder : standardTableauBoxOrder T = standardTableauBoxOrder U) :
    T = U := by
  have hcells : cellOfEntry T = cellOfEntry U := by
    exact List.ofFn_injective horder
  apply standardYoungTableau_ext_entry
  intro u
  let a := T.entry u
  have hcell : cellOfEntry T a = cellOfEntry U a := congrFun hcells a
  have hleft : cellOfEntry T a = u := cellOfEntry_eq_of_entry T rfl
  have hright : U.entry (cellOfEntry U a) = a := entry_cellOfEntry U a
  rw [hleft] at hcell
  have hu : U.entry u = a := by
    calc
      U.entry u = U.entry (cellOfEntry U a) := congrArg U.entry hcell
      _ = a := hright
  exact hu.symm

/-- Incomparable consecutive entry-cells cannot lie in one row. -/
theorem not_adjacentSameRow_of_incomparable
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hinc : Incomparable YoungCellRowColumnLt
      (adjacentLoCell T a) (adjacentHiCell T a)) :
    ¬ adjacentSameRow T a := by
  intro hrow
  have hcol_ne :
      YoungCell.col (adjacentLoCell T a) ≠
        YoungCell.col (adjacentHiCell T a) := by
    intro hcol
    apply adjacentLoCell_ne_hiCell T a
    apply Subtype.ext
    apply Prod.ext
    · exact Fin.ext hrow
    · exact Fin.ext hcol
  rcases lt_or_gt_of_ne hcol_ne with hlt | hgt
  · exact hinc.1 (Or.inl ⟨hrow, hlt⟩)
  · exact hinc.2 (Or.inl ⟨hrow.symm, hgt⟩)

/-- Incomparable consecutive entry-cells cannot lie in one column. -/
theorem not_adjacentSameCol_of_incomparable
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hinc : Incomparable YoungCellRowColumnLt
      (adjacentLoCell T a) (adjacentHiCell T a)) :
    ¬ adjacentSameCol T a := by
  intro hcol
  have hrow_ne :
      YoungCell.row (adjacentLoCell T a) ≠
        YoungCell.row (adjacentHiCell T a) := by
    intro hrow
    apply adjacentLoCell_ne_hiCell T a
    apply Subtype.ext
    apply Prod.ext
    · exact Fin.ext hrow
    · exact Fin.ext hcol
  rcases lt_or_gt_of_ne hrow_ne with hlt | hgt
  · exact hinc.1 (Or.inr ⟨hcol, hlt⟩)
  · exact hinc.2 (Or.inr ⟨hcol.symm, hgt⟩)

/-- Swapping adjacent tableau entries swaps exactly the corresponding two
positions in the box-order list. -/
theorem standardTableauBoxOrder_adjacentSwap
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow : YoungCell.row (adjacentLoCell T a) ≠
      YoungCell.row (adjacentHiCell T a))
    (hcol : YoungCell.col (adjacentLoCell T a) ≠
      YoungCell.col (adjacentHiCell T a)) :
    standardTableauBoxOrder (adjacentSwapTableau T a hrow hcol) =
      ((standardTableauBoxOrder T).set (a : Nat) (adjacentHiCell T a)).set
        ((a : Nat) + 1) (adjacentLoCell T a) := by
  apply List.ext_getElem
  · simp
  · intro i hi_left hi_right
    have hi : i < n + 1 := by
      simpa [standardTableauBoxOrder] using hi_left
    let b : Fin (n + 1) := ⟨i, hi⟩
    by_cases hb_lo : b = adjacentEntryLo a
    · have hi_lo : i = (a : Nat) := congrArg Fin.val hb_lo
      subst i
      simp only [standardTableauBoxOrder, List.getElem_ofFn]
      change cellOfEntry (adjacentSwapTableau T a hrow hcol)
        (adjacentEntryLo a) = _
      rw [adjacentSwapTableau_cell_lo]
      rw [List.getElem_set_of_ne (by omega)]
      simp
    · by_cases hb_hi : b = adjacentEntryHi a
      · have hi_hi : i = (a : Nat) + 1 := by
          simpa [b, adjacentEntryHi] using congrArg Fin.val hb_hi
        subst i
        simp only [standardTableauBoxOrder, List.getElem_ofFn]
        change cellOfEntry (adjacentSwapTableau T a hrow hcol)
          (adjacentEntryHi a) = _
        rw [adjacentSwapTableau_cell_hi]
        simp
      · simp only [standardTableauBoxOrder, List.getElem_ofFn]
        rw [adjacentSwapTableau_cell_of_ne_lo_hi T a hrow hcol hb_lo hb_hi]
        have hi_ne_lo : i ≠ (a : Nat) := by
          intro h
          apply hb_lo
          apply Fin.ext
          simpa [b, adjacentEntryLo] using h
        have hi_ne_hi : i ≠ (a : Nat) + 1 := by
          intro h
          apply hb_hi
          apply Fin.ext
          simpa [b, adjacentEntryHi] using h
        rw [List.getElem_set_of_ne hi_ne_hi.symm,
          List.getElem_set_of_ne hi_ne_lo.symm]
        rw [List.getElem_ofFn]

/-- One edge in the standard-tableau adjacent-swap graph of a fixed shape. -/
def StandardTableauxAdjacent {n : Nat} {lam : YoungDiagram (n + 1)}
    (T U : StandardYoungTableau lam) : Prop :=
  ∃ (a : Fin n) (hrow : ¬ adjacentSameRow T a)
    (hcol : ¬ adjacentSameCol T a),
    U = adjacentSwapTableau T a hrow hcol

/-- One adjacent incomparable swap of a tableau's box-order list is induced by
one valid adjacent swap of tableau entries. -/
theorem standardTableauxAdjacent_of_boxOrder_adjacentSwap
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) {ys : List (YoungCell lam)}
    (hstep : AdjacentIncomparableSwap YoungCellRowColumnLt
      (standardTableauBoxOrder T) ys) :
    ∃ U : StandardYoungTableau lam,
      StandardTableauxAdjacent T U ∧ standardTableauBoxOrder U = ys := by
  rcases hstep with ⟨pre, post, u, v, hinc, hsource, rfl⟩
  have hlength := congrArg List.length hsource
  simp only [standardTableauBoxOrder_length, List.length_append,
    List.length_cons] at hlength
  have hk : pre.length < n := by omega
  have hk_parent : pre.length < n + 1 := by omega
  have hk_succ_parent : pre.length + 1 < n + 1 := by omega
  let a : Fin n := ⟨pre.length, hk⟩
  have hu_get_opt : (standardTableauBoxOrder T)[pre.length]? = some u := by
    rw [hsource]
    simp
  have hv_get_opt :
      (standardTableauBoxOrder T)[pre.length + 1]? = some v := by
    rw [hsource]
    simp
  have hu_get : cellOfEntry T ⟨pre.length, hk_parent⟩ = u := by
    rw [List.getElem?_eq_getElem (by
      simpa [standardTableauBoxOrder] using hk_parent)] at hu_get_opt
    have hu_list := Option.some.inj hu_get_opt
    simpa only [standardTableauBoxOrder, List.getElem_ofFn] using hu_list
  have hv_get : cellOfEntry T ⟨pre.length + 1, hk_succ_parent⟩ = v := by
    rw [List.getElem?_eq_getElem (by
      simpa [standardTableauBoxOrder] using hk_succ_parent)] at hv_get_opt
    have hv_list := Option.some.inj hv_get_opt
    simpa only [standardTableauBoxOrder, List.getElem_ofFn] using hv_list
  have hu : adjacentLoCell T a = u := by
    simpa [adjacentLoCell, adjacentEntryLo, a] using hu_get
  have hv : adjacentHiCell T a = v := by
    simpa [adjacentHiCell, adjacentEntryHi, a] using hv_get
  have hinc' : Incomparable YoungCellRowColumnLt
      (adjacentLoCell T a) (adjacentHiCell T a) := by
    simpa [hu, hv] using hinc
  have hrow : ¬ adjacentSameRow T a :=
    not_adjacentSameRow_of_incomparable T a hinc'
  have hcol : ¬ adjacentSameCol T a :=
    not_adjacentSameCol_of_incomparable T a hinc'
  let U := adjacentSwapTableau T a hrow hcol
  refine ⟨U, ⟨a, hrow, hcol, rfl⟩, ?_⟩
  dsimp [U]
  rw [standardTableauBoxOrder_adjacentSwap]
  rw [hsource]
  simp [a, hu, hv]

/-- A finite path of adjacent incomparable box-order swaps lifts to a finite
path of valid adjacent tableau swaps. -/
theorem standardTableauxPath_of_boxOrderPath
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) {ys : List (YoungCell lam)}
    (hreach : LinearExtensionSwapReachable YoungCellRowColumnLt
      (standardTableauBoxOrder T) ys) :
    ∃ U : StandardYoungTableau lam,
      Relation.ReflTransGen (StandardTableauxAdjacent (lam := lam)) T U ∧
        standardTableauBoxOrder U = ys := by
  induction hreach with
  | refl =>
      exact ⟨T, Relation.ReflTransGen.refl, rfl⟩
  | tail hxy hyz ih =>
      rcases ih with ⟨U, hTU, hUorder⟩
      rw [← hUorder] at hyz
      rcases standardTableauxAdjacent_of_boxOrder_adjacentSwap U hyz with
        ⟨V, hUV, hVorder⟩
      exact ⟨V, hTU.tail hUV, hVorder⟩

/-- Lemma 5.4 connectedness statement: any two standard tableaux of the same
shape are connected by adjacent swaps that remain standard. -/
def StandardTableauxSwapConnectedStatement : Prop :=
  ∀ {n : Nat} (lam : YoungDiagram (n + 1))
    (T U : StandardYoungTableau lam),
    Relation.ReflTransGen (StandardTableauxAdjacent (lam := lam)) T U

/-- The adjacent-swap graph of standard tableaux of every fixed
Young shape is connected. -/
theorem standardTableauxSwapConnected :
    StandardTableauxSwapConnectedStatement := by
  intro n lam T U
  have hreach : LinearExtensionSwapReachable YoungCellRowColumnLt
      (standardTableauBoxOrder T) (standardTableauBoxOrder U) :=
    linearExtensions_connected_by_adjacent_incomparable_swaps
      YoungCellRowColumnLt
      (standardTableauBoxOrder T) (standardTableauBoxOrder U)
      (standardTableauBoxOrder_isLinearExtension T)
      (standardTableauBoxOrder_isLinearExtension U)
      (standardTableauBoxOrder_perm T U)
  rcases standardTableauxPath_of_boxOrderPath T hreach with
    ⟨V, hTV, hVorder⟩
  have hVU : V = U := standardTableauBoxOrder_injective hVorder
  subst V
  exact hTV

/-- Paper Lemma 5.4: standard tableaux of a fixed shape are connected by valid
adjacent swaps. -/
theorem S05_Lem5_04_standardTableauxSwapConnectedness :
    StandardTableauxSwapConnectedStatement :=
  standardTableauxSwapConnected

end DictatorshipTesting
