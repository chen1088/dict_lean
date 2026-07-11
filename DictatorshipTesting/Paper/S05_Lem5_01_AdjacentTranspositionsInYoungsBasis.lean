import DictatorshipTesting.Paper.S05_Int_YoungOrthogonal

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_02_DiagonalContentEigenspaces`
- `DictatorshipTesting.Paper.S05_Int_AdjacentCoxeterPresentation`
-/


/-!
Paper statement: Lemma 5.1 (`lem:young-adjacent-matrices`)
Title in paper: Tableau Coxeter model for adjacent transpositions.

Status: proven. This file formalizes the concrete tableau-coordinate Young orthogonal
adjacent-transposition formula: the same-row and same-column diagonal cases,
the swappable two-by-two block, its `+1` and `-1` eigenvectors, and the Coxeter
relations for these adjacent operators.  It deliberately does not assert the
external Specht-module classification theorem.

The adjacent-word action model is included here because Lemma 5.1 is its only
paper-facing user.
-/

noncomputable section

namespace DictatorshipTesting

/-- A concrete adjacent-generator action model for a Young diagram. -/
structure YoungAdjacentActionModel {n : Nat}
    (lam : YoungDiagram (n + 1)) where
  op : Fin n -> TableauSpace lam -> TableauSpace lam
  involutive :
    forall (i : Fin n) f, op i (op i f) = f
  commute_disjoint :
    forall (i j : Fin n), adjacentIndexDisjoint i j ->
      forall f, op i (op j f) = op j (op i f)
  braid_of_succ :
    forall (i j : Fin n), (j : Nat) = (i : Nat) + 1 ->
      forall f, op i (op j (op i f)) = op j (op i (op j f))

/-- The Young adjacent action model supplied by the concrete Young orthogonal
adjacent operators. -/
def youngAdjacentActionModel {n : Nat}
    (lam : YoungDiagram (n + 1)) :
    YoungAdjacentActionModel lam where
  op := youngAdjacentOperator
  involutive := by
    intro i f
    exact youngAdjacentOperator_sq i f
  commute_disjoint := by
    intro i j hdisj f
    exact youngAdjacentOperator_comm_of_disjoint_indices i j hdisj f
  braid_of_succ := by
    intro i j hsucc f
    exact youngAdjacentOperator_braid_of_succ i j hsucc f

@[simp] theorem youngAdjacentActionModel_op {n : Nat}
    (lam : YoungDiagram (n + 1)) :
    (youngAdjacentActionModel lam).op = youngAdjacentOperator := rfl

/-- Words in adjacent generators for `S_{n+1}`.  The letter `i : Fin n`
corresponds to the adjacent transposition swapping `i` and `i+1`. -/
abbrev AdjacentWord (n : Nat) := List (Fin n)

/-- Operator associated to a word in adjacent generators.  The head of the list
acts last on the written vector expression, i.e. `[i,j]` denotes
`s_i s_j` as a left action. -/
def youngAdjacentWordOperator {n : Nat}
    {lam : YoungDiagram (n + 1)} :
    AdjacentWord n -> TableauSpace lam -> TableauSpace lam
  | [], f => f
  | i :: w, f => youngAdjacentOperator i (youngAdjacentWordOperator w f)

@[simp] theorem youngAdjacentWordOperator_nil {n : Nat}
    {lam : YoungDiagram (n + 1)} (f : TableauSpace lam) :
    youngAdjacentWordOperator ([] : AdjacentWord n) f = f := rfl

@[simp] theorem youngAdjacentWordOperator_cons {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (i : Fin n) (w : AdjacentWord n) (f : TableauSpace lam) :
    youngAdjacentWordOperator (i :: w) f =
      youngAdjacentOperator i (youngAdjacentWordOperator w f) := rfl

theorem youngAdjacentWordOperator_append {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (w v : AdjacentWord n) (f : TableauSpace lam) :
    youngAdjacentWordOperator (w ++ v) f =
      youngAdjacentWordOperator w (youngAdjacentWordOperator v f) := by
  induction w with
  | nil =>
      rfl
  | cons i w ih =>
      simp [youngAdjacentWordOperator, ih]

theorem youngAdjacentWordOperator_cancel_pair {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (i : Fin n) (w : AdjacentWord n) (f : TableauSpace lam) :
    youngAdjacentWordOperator (i :: i :: w) f =
      youngAdjacentWordOperator w f := by
  change youngAdjacentOperator i
      (youngAdjacentOperator i (youngAdjacentWordOperator w f)) =
    youngAdjacentWordOperator w f
  exact youngAdjacentOperator_sq i (youngAdjacentWordOperator w f)

theorem youngAdjacentWordOperator_swap_disjoint {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (i j : Fin n) (hdisj : adjacentIndexDisjoint i j)
    (w : AdjacentWord n) (f : TableauSpace lam) :
    youngAdjacentWordOperator (i :: j :: w) f =
      youngAdjacentWordOperator (j :: i :: w) f := by
  change youngAdjacentOperator i
      (youngAdjacentOperator j (youngAdjacentWordOperator w f)) =
    youngAdjacentOperator j
      (youngAdjacentOperator i (youngAdjacentWordOperator w f))
  exact youngAdjacentOperator_comm_of_disjoint_indices
    i j hdisj (youngAdjacentWordOperator w f)

theorem youngAdjacentWordOperator_braid_move_of_succ {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (i j : Fin n) (hsucc : (j : Nat) = (i : Nat) + 1)
    (w : AdjacentWord n) (f : TableauSpace lam) :
    youngAdjacentWordOperator (i :: j :: i :: w) f =
      youngAdjacentWordOperator (j :: i :: j :: w) f := by
  change youngAdjacentOperator i
      (youngAdjacentOperator j
        (youngAdjacentOperator i (youngAdjacentWordOperator w f))) =
    youngAdjacentOperator j
      (youngAdjacentOperator i
        (youngAdjacentOperator j (youngAdjacentWordOperator w f)))
  exact youngAdjacentOperator_braid_of_succ
    i j hsucc (youngAdjacentWordOperator w f)

namespace AdjacentWord

/-- One elementary Coxeter move on adjacent words, allowing a move under a
common left context by repeated `context_cons`. -/
inductive CoxeterStep {n : Nat} :
    AdjacentWord n -> AdjacentWord n -> Prop
  | cancel_pair (i : Fin n) (w : AdjacentWord n) :
      CoxeterStep (i :: i :: w) w
  | swap_disjoint (i j : Fin n) (w : AdjacentWord n)
      (hdisj : adjacentIndexDisjoint i j) :
      CoxeterStep (i :: j :: w) (j :: i :: w)
  | braid (i j : Fin n) (w : AdjacentWord n)
      (hsucc : (j : Nat) = (i : Nat) + 1) :
      CoxeterStep (i :: j :: i :: w) (j :: i :: j :: w)
  | context_cons (i : Fin n) {w w' : AdjacentWord n} :
      CoxeterStep w w' -> CoxeterStep (i :: w) (i :: w')

/-- Equivalence relation generated by elementary Coxeter word moves. -/
abbrev CoxeterEquiv {n : Nat} :
    AdjacentWord n -> AdjacentWord n -> Prop :=
  Relation.EqvGen (@CoxeterStep n)

end AdjacentWord

theorem youngAdjacentWordOperator_respects_coxeter_step {n : Nat}
    {lam : YoungDiagram (n + 1)}
    {w w' : AdjacentWord n}
    (h : AdjacentWord.CoxeterStep w w') :
    youngAdjacentWordOperator (lam := lam) w =
      youngAdjacentWordOperator (lam := lam) w' := by
  induction h with
  | cancel_pair i w =>
      funext f
      exact youngAdjacentWordOperator_cancel_pair i w f
  | swap_disjoint i j w hdisj =>
      funext f
      exact youngAdjacentWordOperator_swap_disjoint i j hdisj w f
  | braid i j w hsucc =>
      funext f
      exact youngAdjacentWordOperator_braid_move_of_succ i j hsucc w f
  | context_cons i h ih =>
      funext f
      change youngAdjacentOperator i (youngAdjacentWordOperator _ f) =
        youngAdjacentOperator i (youngAdjacentWordOperator _ f)
      exact congrArg (youngAdjacentOperator i) (congrFun ih f)

theorem youngAdjacentWordOperator_respects_coxeter_equiv {n : Nat}
    {lam : YoungDiagram (n + 1)}
    {w w' : AdjacentWord n}
    (h : AdjacentWord.CoxeterEquiv w w') :
    youngAdjacentWordOperator (lam := lam) w =
      youngAdjacentWordOperator (lam := lam) w' := by
  induction h with
  | rel x y hstep =>
      exact youngAdjacentWordOperator_respects_coxeter_step
        (lam := lam) hstep
  | refl x =>
      rfl
  | symm x y h ih =>
      exact ih.symm
  | trans x y z hxy hyz ihxy ihyz =>
      exact ihxy.trans ihyz

/-- The actual adjacent transposition of `Fin (n+1)` corresponding to a
generator index `i : Fin n`. -/
def adjacentSwapPerm {n : Nat} (i : Fin n) : Equiv.Perm (Fin (n + 1)) where
  toFun := adjacentSwapValue i
  invFun := adjacentSwapValue i
  left_inv := adjacentSwapValue_involutive i
  right_inv := adjacentSwapValue_involutive i

@[simp] theorem adjacentSwapPerm_apply {n : Nat}
    (i : Fin n) (x : Fin (n + 1)) :
    adjacentSwapPerm i x = adjacentSwapValue i x := rfl

/-- Permutation of `Fin (n+1)` represented by a word in adjacent generators,
with the same left-action convention as `youngAdjacentWordOperator`. -/
def adjacentWordPerm {n : Nat} :
    AdjacentWord n -> Equiv.Perm (Fin (n + 1))
  | [] => 1
  | i :: w => adjacentSwapPerm i * adjacentWordPerm w

@[simp] theorem adjacentWordPerm_nil {n : Nat} :
    adjacentWordPerm ([] : AdjacentWord n) =
      (1 : Equiv.Perm (Fin (n + 1))) := rfl

@[simp] theorem adjacentWordPerm_cons {n : Nat}
    (i : Fin n) (w : AdjacentWord n) :
    adjacentWordPerm (i :: w) =
      adjacentSwapPerm i * adjacentWordPerm w := rfl

@[simp] theorem adjacentWordPerm_cons_apply {n : Nat}
    (i : Fin n) (w : AdjacentWord n) (x : Fin (n + 1)) :
    adjacentWordPerm (i :: w) x =
      adjacentSwapValue i (adjacentWordPerm w x) := rfl

theorem adjacentWordPerm_append {n : Nat}
    (w v : AdjacentWord n) :
    adjacentWordPerm (w ++ v) = adjacentWordPerm w * adjacentWordPerm v := by
  induction w with
  | nil =>
      simp [adjacentWordPerm]
  | cons i w ih =>
      simp [adjacentWordPerm, ih, mul_assoc]

theorem adjacentWordPerm_cancel_pair {n : Nat}
    (i : Fin n) (w : AdjacentWord n) :
    adjacentWordPerm (i :: i :: w) = adjacentWordPerm w := by
  ext x
  simp [adjacentWordPerm, adjacentSwapPerm, adjacentSwapValue_involutive]

theorem adjacentWordPerm_swap_disjoint {n : Nat}
    (i j : Fin n) (hdisj : adjacentIndexDisjoint i j)
    (w : AdjacentWord n) :
    adjacentWordPerm (i :: j :: w) =
      adjacentWordPerm (j :: i :: w) := by
  ext x
  simp [adjacentWordPerm, adjacentSwapPerm,
    adjacentSwapValue_comm_of_disjoint_indices i j hdisj]

theorem adjacentWordPerm_braid_move_of_succ {n : Nat}
    (i j : Fin n) (hsucc : (j : Nat) = (i : Nat) + 1)
    (w : AdjacentWord n) :
    adjacentWordPerm (i :: j :: i :: w) =
      adjacentWordPerm (j :: i :: j :: w) := by
  ext x
  simp [adjacentWordPerm, adjacentSwapPerm,
    adjacentSwapValue_braid_of_succ i j hsucc]

theorem adjacentWordPerm_respects_coxeter_step {n : Nat}
    {w w' : AdjacentWord n}
    (h : AdjacentWord.CoxeterStep w w') :
    adjacentWordPerm w = adjacentWordPerm w' := by
  induction h with
  | cancel_pair i w =>
      exact adjacentWordPerm_cancel_pair i w
  | swap_disjoint i j w hdisj =>
      exact adjacentWordPerm_swap_disjoint i j hdisj w
  | braid i j w hsucc =>
      exact adjacentWordPerm_braid_move_of_succ i j hsucc w
  | context_cons i h ih =>
      simp [adjacentWordPerm, ih]

theorem adjacentWordPerm_respects_coxeter_equiv {n : Nat}
    {w w' : AdjacentWord n}
    (h : AdjacentWord.CoxeterEquiv w w') :
    adjacentWordPerm w = adjacentWordPerm w' := by
  induction h with
  | rel x y hstep =>
      exact adjacentWordPerm_respects_coxeter_step hstep
  | refl x =>
      rfl
  | symm x y h ih =>
      exact ih.symm
  | trans x y z hxy hyz ihxy ihyz =>
      exact ihxy.trans ihyz

/-- Setoid on adjacent words generated by Coxeter moves. -/
def adjacentWordCoxeterSetoid (n : Nat) : Setoid (AdjacentWord n) where
  r := AdjacentWord.CoxeterEquiv
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro w
      exact Relation.EqvGen.refl w
    · intro w w' h
      exact Relation.EqvGen.symm w w' h
    · intro u v w huv hvw
      exact Relation.EqvGen.trans u v w huv hvw

/-- The formal Coxeter-word quotient generated by adjacent-transposition
relations.  This is a presented-word object, not yet identified with
`Perm (Fin (n+1))`. -/
abbrev AdjacentCoxeterClass (n : Nat) :=
  Quotient (adjacentWordCoxeterSetoid n)

namespace AdjacentCoxeterClass

/-- The quotient class of an adjacent word. -/
def mk {n : Nat} (w : AdjacentWord n) : AdjacentCoxeterClass n :=
  Quotient.mk (adjacentWordCoxeterSetoid n) w

end AdjacentCoxeterClass

/-- The Young adjacent operator descends from adjacent words to Coxeter-word
classes. -/
def youngAdjacentCoxeterClassOperator {n : Nat}
    {lam : YoungDiagram (n + 1)} :
    AdjacentCoxeterClass n -> TableauSpace lam -> TableauSpace lam :=
  Quotient.lift (youngAdjacentWordOperator (lam := lam)) (by
    intro w w' h
    exact youngAdjacentWordOperator_respects_coxeter_equiv (lam := lam) h)

@[simp] theorem youngAdjacentCoxeterClassOperator_mk {n : Nat}
    {lam : YoungDiagram (n + 1)} (w : AdjacentWord n) :
    youngAdjacentCoxeterClassOperator (lam := lam)
        (AdjacentCoxeterClass.mk w) =
      youngAdjacentWordOperator (lam := lam) w := rfl

/-- The adjacent-word permutation shadow also descends to Coxeter-word
classes. -/
def adjacentCoxeterClassPerm {n : Nat} :
    AdjacentCoxeterClass n -> Equiv.Perm (Fin (n + 1)) :=
  Quotient.lift adjacentWordPerm (by
    intro w w' h
    exact adjacentWordPerm_respects_coxeter_equiv h)

@[simp] theorem adjacentCoxeterClassPerm_mk {n : Nat}
    (w : AdjacentWord n) :
    adjacentCoxeterClassPerm (AdjacentCoxeterClass.mk w) =
      adjacentWordPerm w := rfl

/-- Lemma 5.1 basis-level component: adjacent entries occupy distinct cells. -/
theorem S05_Lem5_01_adjacent_cells_distinct {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) :
    adjacentLoCell T a ≠ adjacentHiCell T a := by
  exact adjacentLoCell_ne_hiCell T a

/-- Lemma 5.1 basis-level component: in a common row, the lower adjacent entry
is to the left. -/
theorem S05_Lem5_01_adjacent_col_lt_of_sameRow {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow :
      YoungCell.row (adjacentLoCell T a) =
        YoungCell.row (adjacentHiCell T a)) :
    YoungCell.col (adjacentLoCell T a) <
      YoungCell.col (adjacentHiCell T a) := by
  exact adjacent_col_lt_of_sameRow T a hrow

/-- Lemma 5.1 basis-level component: in a common column, the lower adjacent
entry is above. -/
theorem S05_Lem5_01_adjacent_row_lt_of_sameCol {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol :
      YoungCell.col (adjacentLoCell T a) =
        YoungCell.col (adjacentHiCell T a)) :
      YoungCell.row (adjacentLoCell T a) <
        YoungCell.row (adjacentHiCell T a) := by
  exact adjacent_row_lt_of_sameCol T a hcol

/-- Lemma 5.1 basis-level component: same-row adjacent entries occupy
neighboring columns. -/
theorem S05_Lem5_01_adjacent_col_eq_succ_of_sameRow {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow :
      YoungCell.row (adjacentLoCell T a) =
        YoungCell.row (adjacentHiCell T a)) :
    YoungCell.col (adjacentHiCell T a) =
      YoungCell.col (adjacentLoCell T a) + 1 := by
  exact adjacent_col_eq_succ_of_sameRow T a hrow

/-- Lemma 5.1 basis-level component: same-column adjacent entries occupy
neighboring rows. -/
theorem S05_Lem5_01_adjacent_row_eq_succ_of_sameCol {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol :
      YoungCell.col (adjacentLoCell T a) =
        YoungCell.col (adjacentHiCell T a)) :
    YoungCell.row (adjacentHiCell T a) =
      YoungCell.row (adjacentLoCell T a) + 1 := by
  exact adjacent_row_eq_succ_of_sameCol T a hcol

/-- Lemma 5.1 basis-level component: same-row adjacent contents differ by `+1`. -/
theorem S05_Lem5_01_adjacent_content_hi_eq_lo_add_one_of_sameRow {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow :
      YoungCell.row (adjacentLoCell T a) =
        YoungCell.row (adjacentHiCell T a)) :
    YoungCell.content (adjacentHiCell T a) =
      YoungCell.content (adjacentLoCell T a) + 1 := by
  exact adjacent_content_hi_eq_lo_add_one_of_sameRow T a hrow

/-- Lemma 5.1 basis-level component: same-column adjacent contents differ by `-1`. -/
theorem S05_Lem5_01_adjacent_content_hi_eq_lo_sub_one_of_sameCol {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol :
      YoungCell.col (adjacentLoCell T a) =
        YoungCell.col (adjacentHiCell T a)) :
    YoungCell.content (adjacentHiCell T a) =
      YoungCell.content (adjacentLoCell T a) - 1 := by
  exact adjacent_content_hi_eq_lo_sub_one_of_sameCol T a hcol

/-- Lemma 5.1 basis-level component: the adjacent swap sends the lower
adjacent-entry cell to the upper adjacent value. -/
theorem S05_Lem5_01_adjacentSwapEntry_loCell {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) :
    adjacentSwapEntry T a (adjacentLoCell T a) = adjacentEntryHi a := by
  exact adjacentSwapEntry_loCell T a

/-- Lemma 5.1 basis-level component: the adjacent swap sends the upper
adjacent-entry cell to the lower adjacent value. -/
theorem S05_Lem5_01_adjacentSwapEntry_hiCell {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) :
    adjacentSwapEntry T a (adjacentHiCell T a) = adjacentEntryLo a := by
  exact adjacentSwapEntry_hiCell T a

/-- Lemma 5.1 basis-level component: swapping two adjacent values is bijective
on the cell set. -/
theorem S05_Lem5_01_adjacentSwapEntry_bijective {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) :
    Function.Bijective (adjacentSwapEntry T a) := by
  exact adjacentSwapEntry_bijective T a

/-- Lemma 5.1 Coxeter-frontier component: value swaps for distant adjacent
indices commute. -/
theorem S05_Lem5_01_adjacentSwapValue_comm_of_disjoint_indices {n : Nat}
    (a b : Fin n) (hdisj : adjacentIndexDisjoint a b)
    (x : Fin (n + 1)) :
    adjacentSwapValue a (adjacentSwapValue b x) =
      adjacentSwapValue b (adjacentSwapValue a x) := by
  exact adjacentSwapValue_comm_of_disjoint_indices a b hdisj x

/-- Lemma 5.1 Coxeter-frontier component: adjacent value swaps satisfy the
braid relation for consecutive adjacent indices. -/
theorem S05_Lem5_01_adjacentSwapValue_braid_of_succ {n : Nat}
    (a b : Fin n) (hsucc : (b : Nat) = (a : Nat) + 1)
    (x : Fin (n + 1)) :
    adjacentSwapValue a (adjacentSwapValue b (adjacentSwapValue a x)) =
      adjacentSwapValue b (adjacentSwapValue a (adjacentSwapValue b x)) := by
  exact adjacentSwapValue_braid_of_succ a b hsucc x

/-- Lemma 5.1 Coxeter-frontier component: entry functions obtained by distant
adjacent value swaps commute pointwise. -/
theorem S05_Lem5_01_adjacentSwapEntry_comm_of_disjoint_indices {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hdisj : adjacentIndexDisjoint a b) (u : YoungCell lam) :
    adjacentSwapValue a (adjacentSwapEntry T b u) =
      adjacentSwapValue b (adjacentSwapEntry T a u) := by
  exact adjacentSwapEntry_comm_of_disjoint_indices T a b hdisj u

/-- Lemma 5.1 Coxeter-frontier component: entry functions inherit the value
braid relation for consecutive adjacent indices. -/
theorem S05_Lem5_01_adjacentSwapEntry_braid_of_succ {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hsucc : (b : Nat) = (a : Nat) + 1) (u : YoungCell lam) :
    adjacentSwapValue a (adjacentSwapValue b (adjacentSwapEntry T a u)) =
      adjacentSwapValue b (adjacentSwapValue a (adjacentSwapEntry T b u)) := by
  exact adjacentSwapEntry_braid_of_succ T a b hsucc u

/-- Lemma 5.1 basis-level component: if adjacent entries are in different rows
and columns, swapping their values gives another standard tableau. -/
noncomputable def S05_Lem5_01_adjacentSwapTableau {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne :
      YoungCell.row (adjacentLoCell T a) ≠
        YoungCell.row (adjacentHiCell T a))
    (hcol_ne :
      YoungCell.col (adjacentLoCell T a) ≠
        YoungCell.col (adjacentHiCell T a)) :
    StandardYoungTableau lam :=
  adjacentSwapTableau T a hrow_ne hcol_ne

/-- Lemma 5.1 basis-level component: after swapping adjacent values, the lower
entry lies in the old upper cell. -/
theorem S05_Lem5_01_adjacentSwapTableau_cell_lo {n : Nat}
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
  exact adjacentSwapTableau_cell_lo T a hrow_ne hcol_ne

/-- Lemma 5.1 basis-level component: after swapping adjacent values, the upper
entry lies in the old lower cell. -/
theorem S05_Lem5_01_adjacentSwapTableau_cell_hi {n : Nat}
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
  exact adjacentSwapTableau_cell_hi T a hrow_ne hcol_ne

/-- Lemma 5.1 basis-level component: non-adjacent entries keep their cells after
the adjacent swap. -/
theorem S05_Lem5_01_adjacentSwapTableau_cell_of_ne_lo_hi {n : Nat}
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
  exact adjacentSwapTableau_cell_of_ne_lo_hi T a hrow_ne hcol_ne hblo hbhi

/-- Lemma 5.1 basis-level component: after the adjacent swap, the lower entry
has the old upper entry's content. -/
theorem S05_Lem5_01_adjacentSwapTableau_entryContent_lo {n : Nat}
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
  exact adjacentSwapTableau_entryContent_lo T a hrow_ne hcol_ne

/-- Lemma 5.1 basis-level component: after the adjacent swap, the upper entry
has the old lower entry's content. -/
theorem S05_Lem5_01_adjacentSwapTableau_entryContent_hi {n : Nat}
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
  exact adjacentSwapTableau_entryContent_hi T a hrow_ne hcol_ne

/-- Lemma 5.1 basis-level component: non-adjacent entry contents are preserved
by the adjacent swap. -/
theorem S05_Lem5_01_adjacentSwapTableau_entryContent_of_ne_lo_hi {n : Nat}
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
  exact adjacentSwapTableau_entryContent_of_ne_lo_hi T a hrow_ne hcol_ne hblo hbhi

/-- Lemma 5.1 Coxeter-frontier component: distant adjacent tableau swaps
commute, assuming the needed second swaps are standard. -/
theorem S05_Lem5_01_adjacentSwapTableau_comm_of_disjoint_indices {n : Nat}
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
  exact adjacentSwapTableau_comm_of_disjoint_indices
    T a b hdisj hrow_a hcol_a hrow_b hcol_b
    hrow_a_after_b hcol_a_after_b hrow_b_after_a hcol_b_after_a

/-- Lemma 5.1 Coxeter-frontier component: distant adjacent tableau swaps
commute, with the second-swap standardness hypotheses transported
automatically from disjointness. -/
theorem S05_Lem5_01_adjacentSwapTableau_comm_of_disjoint_indices_auto
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
  exact adjacentSwapTableau_comm_of_disjoint_indices_auto
    T a b hdisj hrow_a hcol_a hrow_b hcol_b

/-- Lemma 5.1 coefficient component: the axial distance is `1` in the
same-row case. -/
theorem S05_Lem5_01_adjacentAxialDistance_sameRow {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow : adjacentSameRow T a) :
    adjacentAxialDistance T a = 1 := by
  exact adjacentAxialDistance_sameRow T a hrow

/-- Lemma 5.1 coefficient component: the axial distance is `-1` in the
same-column case. -/
theorem S05_Lem5_01_adjacentAxialDistance_sameCol {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol : adjacentSameCol T a) :
    adjacentAxialDistance T a = -1 := by
  exact adjacentAxialDistance_sameCol T a hcol

/-- Lemma 5.1 coefficient component: swapping a swappable adjacent pair negates
the axial distance. -/
theorem S05_Lem5_01_adjacentAxialDistance_swap_neg {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    adjacentAxialDistance (adjacentSwapTableau T a hrow_ne hcol_ne) a =
      - adjacentAxialDistance T a := by
  exact adjacentAxialDistance_swap_neg T a hrow_ne hcol_ne

/-- Lemma 5.1 Coxeter-frontier component: a distant adjacent swap preserves
the axial distance of the other adjacent pair. -/
theorem S05_Lem5_01_adjacentAxialDistance_after_disjoint_swap_eq
    {n : Nat} {lam : YoungDiagram (n + 1)}
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
  exact adjacentAxialDistance_after_disjoint_swap_eq
    T a b hdisj hrow_b hcol_b

/-- Lemma 5.1 coefficient component: in the swappable case, the axial distance
is nonzero. -/
theorem S05_Lem5_01_adjacentAxialDistance_ne_zero_of_swappable {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    adjacentAxialDistance T a ≠ 0 := by
  exact adjacentAxialDistance_ne_zero_of_swappable T a hrow_ne hcol_ne

/-- Lemma 5.1 coefficient component: the diagonal coefficient is `1` in the
same-row case. -/
theorem S05_Lem5_01_youngAdjacentDiagCoeff_sameRow {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow : adjacentSameRow T a) :
    youngAdjacentDiagCoeff T a = 1 := by
  exact youngAdjacentDiagCoeff_sameRow T a hrow

/-- Lemma 5.1 coefficient component: the diagonal coefficient is `-1` in the
same-column case. -/
theorem S05_Lem5_01_youngAdjacentDiagCoeff_sameCol {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol : adjacentSameCol T a) :
    youngAdjacentDiagCoeff T a = -1 := by
  exact youngAdjacentDiagCoeff_sameCol T a hcol

/-- Lemma 5.1 coefficient component: in the swappable case, the diagonal
coefficient is nonzero. -/
theorem S05_Lem5_01_youngAdjacentDiagCoeff_ne_zero_of_swappable {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentDiagCoeff T a ≠ 0 := by
  exact youngAdjacentDiagCoeff_ne_zero_of_swappable T a hrow_ne hcol_ne

/-- Lemma 5.1 coefficient component: in the swappable case, the diagonal
coefficient has square at most one. -/
theorem S05_Lem5_01_youngAdjacentDiagCoeff_sq_le_one_of_swappable {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentDiagCoeff T a ^ 2 ≤ 1 := by
  exact youngAdjacentDiagCoeff_sq_le_one_of_swappable T a hrow_ne hcol_ne

/-- Lemma 5.1 coefficient component: swapping a swappable adjacent pair negates
the diagonal coefficient. -/
theorem S05_Lem5_01_youngAdjacentDiagCoeff_swap {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentDiagCoeff (adjacentSwapTableau T a hrow_ne hcol_ne) a =
      - youngAdjacentDiagCoeff T a := by
  exact youngAdjacentDiagCoeff_swap T a hrow_ne hcol_ne

/-- Lemma 5.1 Coxeter-frontier component: a distant adjacent swap preserves
the diagonal coefficient of the other adjacent pair. -/
theorem S05_Lem5_01_youngAdjacentDiagCoeff_after_disjoint_swap_eq
    {n : Nat} {lam : YoungDiagram (n + 1)}
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
  exact youngAdjacentDiagCoeff_after_disjoint_swap_eq
    T a b hdisj hrow_b hcol_b

/-- Lemma 5.1 coefficient component: swapping a swappable adjacent pair
preserves the off-diagonal coefficient. -/
theorem S05_Lem5_01_youngAdjacentOffCoeff_swap {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentOffCoeff (adjacentSwapTableau T a hrow_ne hcol_ne) a =
      youngAdjacentOffCoeff T a := by
  exact youngAdjacentOffCoeff_swap T a hrow_ne hcol_ne

/-- Lemma 5.1 Coxeter-frontier component: a distant adjacent swap preserves
the off-diagonal coefficient of the other adjacent pair. -/
theorem S05_Lem5_01_youngAdjacentOffCoeff_after_disjoint_swap_eq
    {n : Nat} {lam : YoungDiagram (n + 1)}
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
  exact youngAdjacentOffCoeff_after_disjoint_swap_eq
    T a b hdisj hrow_b hcol_b

/-- Lemma 5.1 coefficient component: the off-diagonal coefficient is
nonnegative by construction. -/
theorem S05_Lem5_01_youngAdjacentOffCoeff_nonneg {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) :
    0 ≤ youngAdjacentOffCoeff T a := by
  exact youngAdjacentOffCoeff_nonneg T a

/-- Lemma 5.1 coefficient component: the Young 2-by-2 coefficient squares sum
to one once the square-root radicand is known to be nonnegative. -/
theorem S05_Lem5_01_youngAdjacentCoeff_sq_sum_of_nonneg {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (h :
      0 ≤ 1 - youngAdjacentDiagCoeff T a ^ 2) :
    youngAdjacentDiagCoeff T a ^ 2 +
        youngAdjacentOffCoeff T a ^ 2 = 1 := by
  exact youngAdjacentCoeff_sq_sum_of_nonneg T a h

/-- Lemma 5.1 coefficient component: in the swappable case, the Young 2-by-2
coefficient squares sum to one. -/
theorem S05_Lem5_01_youngAdjacentCoeff_sq_sum_of_swappable {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentDiagCoeff T a ^ 2 +
        youngAdjacentOffCoeff T a ^ 2 = 1 := by
  exact youngAdjacentCoeff_sq_sum_of_swappable T a hrow_ne hcol_ne

/-- Lemma 5.1 matrix-coefficient component: same-row adjacent pairs act
diagonally with coefficient `1` on their tableau. -/
theorem S05_Lem5_01_youngAdjacentMatrixCoeff_sameRow_self {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow : adjacentSameRow T a) :
    youngAdjacentMatrixCoeff a T T = 1 := by
  exact youngAdjacentMatrixCoeff_sameRow_self T a hrow

/-- Lemma 5.1 matrix-coefficient component: same-row adjacent pairs have no
off-diagonal support. -/
theorem S05_Lem5_01_youngAdjacentMatrixCoeff_sameRow_ne {n : Nat}
    {lam : YoungDiagram (n + 1)}
    {S T : StandardYoungTableau lam} (a : Fin n)
    (hrow : adjacentSameRow T a) (hST : S ≠ T) :
    youngAdjacentMatrixCoeff a S T = 0 := by
  exact youngAdjacentMatrixCoeff_sameRow_ne a hrow hST

/-- Lemma 5.1 matrix-coefficient component: same-column adjacent pairs act
diagonally with coefficient `-1` on their tableau. -/
theorem S05_Lem5_01_youngAdjacentMatrixCoeff_sameCol_self {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol : adjacentSameCol T a) :
    youngAdjacentMatrixCoeff a T T = -1 := by
  exact youngAdjacentMatrixCoeff_sameCol_self T a hcol

/-- Lemma 5.1 matrix-coefficient component: same-column adjacent pairs have no
off-diagonal support. -/
theorem S05_Lem5_01_youngAdjacentMatrixCoeff_sameCol_ne {n : Nat}
    {lam : YoungDiagram (n + 1)}
    {S T : StandardYoungTableau lam} (a : Fin n)
    (hcol : adjacentSameCol T a) (hST : S ≠ T) :
    youngAdjacentMatrixCoeff a S T = 0 := by
  exact youngAdjacentMatrixCoeff_sameCol_ne a hcol hST

/-- Lemma 5.1 matrix-coefficient component: in the swappable case, the
coefficient at `T` is the diagonal axial coefficient. -/
theorem S05_Lem5_01_youngAdjacentMatrixCoeff_swappable_self {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentMatrixCoeff a T T = youngAdjacentDiagCoeff T a := by
  exact youngAdjacentMatrixCoeff_swappable_self T a hrow_ne hcol_ne

/-- Lemma 5.1 matrix-coefficient component: in the swappable case, the
coefficient at the swapped tableau is the off-diagonal axial coefficient. -/
theorem S05_Lem5_01_youngAdjacentMatrixCoeff_swappable_swap {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentMatrixCoeff a
        (adjacentSwapTableau T a hrow_ne hcol_ne) T =
      youngAdjacentOffCoeff T a := by
  exact youngAdjacentMatrixCoeff_swappable_swap T a hrow_ne hcol_ne

/-- Lemma 5.1 matrix-coefficient component: the reverse off-diagonal
coefficient in the swappable two-tableau block is the same. -/
theorem S05_Lem5_01_youngAdjacentMatrixCoeff_swappable_swap_symm {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentMatrixCoeff a T
        (adjacentSwapTableau T a hrow_ne hcol_ne) =
      youngAdjacentOffCoeff T a := by
  exact youngAdjacentMatrixCoeff_swappable_swap_symm T a hrow_ne hcol_ne

/-- Lemma 5.1 self-adjointness component: the two off-diagonal matrix
coefficients in a swappable tableau pair agree. -/
theorem S05_Lem5_01_youngAdjacentMatrixCoeff_swappable_pair_symmetric
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentMatrixCoeff a
        (adjacentSwapTableau T a hrow_ne hcol_ne) T =
      youngAdjacentMatrixCoeff a T
        (adjacentSwapTableau T a hrow_ne hcol_ne) := by
  exact youngAdjacentMatrixCoeff_swappable_pair_symmetric T a hrow_ne hcol_ne

/-- Lemma 5.1 matrix-coefficient component: in the swappable case, all other
tableaux have coefficient zero. -/
theorem S05_Lem5_01_youngAdjacentMatrixCoeff_swappable_other {n : Nat}
    {lam : YoungDiagram (n + 1)}
    {S T : StandardYoungTableau lam} (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a)
    (hST : S ≠ T)
    (hSswap : S ≠ adjacentSwapTableau T a hrow_ne hcol_ne) :
    youngAdjacentMatrixCoeff a S T = 0 := by
  exact youngAdjacentMatrixCoeff_swappable_other a hrow_ne hcol_ne hST hSswap

/-- Lemma 5.1 self-adjointness component: if the source tableau is a same-row
diagonal case, its matrix coefficient is symmetric against every target. -/
theorem S05_Lem5_01_youngAdjacentMatrixCoeff_symmetric_of_source_sameRow
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (S T : StandardYoungTableau lam) (a : Fin n)
    (hrowT : adjacentSameRow T a) :
    youngAdjacentMatrixCoeff a S T =
      youngAdjacentMatrixCoeff a T S := by
  exact youngAdjacentMatrixCoeff_symmetric_of_source_sameRow S T a hrowT

/-- Lemma 5.1 self-adjointness component: if the source tableau is a
same-column diagonal case, its matrix coefficient is symmetric against every
target. -/
theorem S05_Lem5_01_youngAdjacentMatrixCoeff_symmetric_of_source_sameCol
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (S T : StandardYoungTableau lam) (a : Fin n)
    (hcolT : adjacentSameCol T a) :
    youngAdjacentMatrixCoeff a S T =
      youngAdjacentMatrixCoeff a T S := by
  exact youngAdjacentMatrixCoeff_symmetric_of_source_sameCol S T a hcolT

/-- Lemma 5.1 self-adjointness component: the concrete Young adjacent matrix
coefficients are symmetric. -/
theorem S05_Lem5_01_youngAdjacentMatrixCoeff_symmetric
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (a : Fin n) (S T : StandardYoungTableau lam) :
    youngAdjacentMatrixCoeff a S T =
      youngAdjacentMatrixCoeff a T S := by
  exact youngAdjacentMatrixCoeff_symmetric a S T

/-- Lemma 5.1 operator component: in the same-row case, the adjacent operator
fixes the tableau basis vector. -/
theorem S05_Lem5_01_youngAdjacentOperator_basis_sameRow {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow : adjacentSameRow T a) :
    youngAdjacentOperator a (tableauBasisVec T) = tableauBasisVec T := by
  exact youngAdjacentOperator_basis_sameRow T a hrow

/-- Lemma 5.1 operator component: in the same-column case, the adjacent
operator negates the tableau basis vector. -/
theorem S05_Lem5_01_youngAdjacentOperator_basis_sameCol {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol : adjacentSameCol T a) :
    youngAdjacentOperator a (tableauBasisVec T) =
      fun S => - tableauBasisVec T S := by
  exact youngAdjacentOperator_basis_sameCol T a hcol

/-- Lemma 5.1 operator component: in the swappable case, the value at `T` is
the diagonal coefficient. -/
theorem S05_Lem5_01_youngAdjacentOperator_basis_swappable_self_value {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentOperator a (tableauBasisVec T) T =
      youngAdjacentDiagCoeff T a := by
  exact youngAdjacentOperator_basis_swappable_self_value T a hrow_ne hcol_ne

/-- Lemma 5.1 operator component: in the swappable case, the value at the
swapped tableau is the off-diagonal coefficient. -/
theorem S05_Lem5_01_youngAdjacentOperator_basis_swappable_swap_value {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentOperator a (tableauBasisVec T)
        (adjacentSwapTableau T a hrow_ne hcol_ne) =
      youngAdjacentOffCoeff T a := by
  exact youngAdjacentOperator_basis_swappable_swap_value T a hrow_ne hcol_ne

/-- Lemma 5.1 operator component: in the swappable case, applying the operator
to the swapped basis vector has the same off-diagonal coordinate at `T`. -/
theorem S05_Lem5_01_youngAdjacentOperator_basis_swappable_swap_symm_value
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentOperator a
        (tableauBasisVec (adjacentSwapTableau T a hrow_ne hcol_ne)) T =
      youngAdjacentOffCoeff T a := by
  exact youngAdjacentOperator_basis_swappable_swap_symm_value
    T a hrow_ne hcol_ne

/-- Lemma 5.1 self-adjointness component: the adjacent operator is symmetric on
the two basis vectors in a swappable tableau pair. -/
theorem S05_Lem5_01_youngAdjacentOperator_selfAdjoint_basis_swappable_pair
    {n : Nat} {lam : YoungDiagram (n + 1)}
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
  exact youngAdjacentOperator_selfAdjoint_basis_swappable_pair
    T a hrow_ne hcol_ne

/-- Lemma 5.1 self-adjointness component: the adjacent operator is
self-adjoint on coordinate basis vectors. -/
theorem S05_Lem5_01_youngAdjacentOperator_selfAdjoint_basis
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (a : Fin n) (S T : StandardYoungTableau lam) :
    tableauInner
        (youngAdjacentOperator a (tableauBasisVec T))
        (tableauBasisVec S) =
      tableauInner
        (tableauBasisVec T)
        (youngAdjacentOperator a (tableauBasisVec S)) := by
  exact youngAdjacentOperator_selfAdjoint_basis a S T

/-- Lemma 5.1 operator component: in the swappable case, all other basis
coordinates vanish. -/
theorem S05_Lem5_01_youngAdjacentOperator_basis_swappable_other_value {n : Nat}
    {lam : YoungDiagram (n + 1)}
    {S T : StandardYoungTableau lam} (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a)
    (hST : S ≠ T)
    (hSswap : S ≠ adjacentSwapTableau T a hrow_ne hcol_ne) :
    youngAdjacentOperator a (tableauBasisVec T) S = 0 := by
  exact youngAdjacentOperator_basis_swappable_other_value
    a hrow_ne hcol_ne hST hSswap

/-- Lemma 5.1 operator component: in the swappable case, the adjacent operator
has support exactly in the two-tableau span generated by `T` and its adjacent
swap. -/
theorem S05_Lem5_01_youngAdjacentOperator_basis_swappable_eq {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentOperator a (tableauBasisVec T) =
      fun S =>
        youngAdjacentDiagCoeff T a * tableauBasisVec T S +
          youngAdjacentOffCoeff T a *
            tableauBasisVec (adjacentSwapTableau T a hrow_ne hcol_ne) S := by
  exact youngAdjacentOperator_basis_swappable_eq T a hrow_ne hcol_ne

/-- Lemma 5.1 operator component: in the swappable case, the swapped tableau
basis vector gives the second column of the two-by-two Young orthogonal block. -/
theorem S05_Lem5_01_youngAdjacentOperator_basis_swappable_swap_eq {n : Nat}
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
  exact youngAdjacentOperator_basis_swappable_swap_eq T a hrow_ne hcol_ne

/-- Lemma 5.1 coefficient component: in the genuine two-tableau case the
diagonal coefficient has square strictly below `1`. -/
theorem S05_Lem5_01_youngAdjacentDiagCoeff_sq_lt_one_of_swappable {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentDiagCoeff T a ^ 2 < 1 := by
  exact youngAdjacentDiagCoeff_sq_lt_one_of_swappable T a hrow_ne hcol_ne

/-- Lemma 5.1 coefficient component: in the genuine two-tableau case the
off-diagonal coefficient is positive. -/
theorem S05_Lem5_01_youngAdjacentOffCoeff_pos_of_swappable {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    0 < youngAdjacentOffCoeff T a := by
  exact youngAdjacentOffCoeff_pos_of_swappable T a hrow_ne hcol_ne

/-- Lemma 5.1 coefficient component: in the genuine two-tableau case the
off-diagonal coefficient is nonzero. -/
theorem S05_Lem5_01_youngAdjacentOffCoeff_ne_zero_of_swappable {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentOffCoeff T a ≠ 0 := by
  exact youngAdjacentOffCoeff_ne_zero_of_swappable T a hrow_ne hcol_ne

/-- Lemma 5.1 eigenline component: in the swappable two-tableau block, the
explicit vector `b e_T + (1-a)e_{T'}` has eigenvalue `+1`. -/
theorem S05_Lem5_01_youngAdjacentOperator_swappable_eigen_plus {n : Nat}
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
  exact youngAdjacentOperator_swappable_eigen_plus T a hrow_ne hcol_ne

/-- Lemma 5.1 eigenline component: the displayed `+1` eigenvector in the
swappable block is nonzero. -/
theorem S05_Lem5_01_youngAdjacentOperator_swappable_eigen_plus_ne_zero {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    (fun S =>
          youngAdjacentOffCoeff T a * tableauBasisVec T S +
            (1 - youngAdjacentDiagCoeff T a) *
              tableauBasisVec (adjacentSwapTableau T a hrow_ne hcol_ne) S)
      ≠ (0 : TableauSpace lam) := by
  exact youngAdjacentOperator_swappable_eigen_plus_ne_zero T a hrow_ne hcol_ne

/-- Lemma 5.1 eigenline component: in the swappable two-tableau block, the
explicit vector `b e_T - (1+a)e_{T'}` has eigenvalue `-1`. -/
theorem S05_Lem5_01_youngAdjacentOperator_swappable_eigen_minus {n : Nat}
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
  exact youngAdjacentOperator_swappable_eigen_minus T a hrow_ne hcol_ne

/-- Lemma 5.1 eigenline component: the displayed `-1` eigenvector in the
swappable block is nonzero. -/
theorem S05_Lem5_01_youngAdjacentOperator_swappable_eigen_minus_ne_zero {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    (fun S =>
          youngAdjacentOffCoeff T a * tableauBasisVec T S -
            (1 + youngAdjacentDiagCoeff T a) *
              tableauBasisVec (adjacentSwapTableau T a hrow_ne hcol_ne) S)
      ≠ (0 : TableauSpace lam) := by
  exact youngAdjacentOperator_swappable_eigen_minus_ne_zero T a hrow_ne hcol_ne

/-- Lemma 5.1, bundled Young orthogonal adjacent-transposition formula in
tableau coordinates.  In the swappable case this is exactly the block
`[[a,b],[b,-a]]`, together with `a^2+b^2=1` and explicit `+1`/`-1`
eigenvectors. -/
theorem S05_Lem5_01_youngAdjacent_matrices {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) :
    (adjacentSameRow T a →
      youngAdjacentOperator a (tableauBasisVec T) = tableauBasisVec T) ∧
    (adjacentSameCol T a →
      youngAdjacentOperator a (tableauBasisVec T) =
        fun S => - tableauBasisVec T S) ∧
    (∀ hrow_ne : ¬ adjacentSameRow T a,
      ∀ hcol_ne : ¬ adjacentSameCol T a,
        youngAdjacentOperator a (tableauBasisVec T) =
          (fun S =>
            youngAdjacentDiagCoeff T a * tableauBasisVec T S +
              youngAdjacentOffCoeff T a *
                tableauBasisVec
                  (adjacentSwapTableau T a hrow_ne hcol_ne) S) ∧
        youngAdjacentOperator a
            (tableauBasisVec
              (adjacentSwapTableau T a hrow_ne hcol_ne)) =
          (fun S =>
            youngAdjacentOffCoeff T a * tableauBasisVec T S -
              youngAdjacentDiagCoeff T a *
                tableauBasisVec
                  (adjacentSwapTableau T a hrow_ne hcol_ne) S) ∧
        youngAdjacentDiagCoeff T a ^ 2 +
            youngAdjacentOffCoeff T a ^ 2 = 1 ∧
        youngAdjacentOperator a
            (fun S =>
              youngAdjacentOffCoeff T a * tableauBasisVec T S +
                (1 - youngAdjacentDiagCoeff T a) *
                  tableauBasisVec
                    (adjacentSwapTableau T a hrow_ne hcol_ne) S) =
          (fun S =>
            youngAdjacentOffCoeff T a * tableauBasisVec T S +
              (1 - youngAdjacentDiagCoeff T a) *
                tableauBasisVec
                  (adjacentSwapTableau T a hrow_ne hcol_ne) S) ∧
        youngAdjacentOperator a
            (fun S =>
              youngAdjacentOffCoeff T a * tableauBasisVec T S -
                (1 + youngAdjacentDiagCoeff T a) *
                  tableauBasisVec
                    (adjacentSwapTableau T a hrow_ne hcol_ne) S) =
          (fun S =>
            - (youngAdjacentOffCoeff T a * tableauBasisVec T S -
                (1 + youngAdjacentDiagCoeff T a) *
                  tableauBasisVec
                    (adjacentSwapTableau T a hrow_ne hcol_ne) S))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hrow
    exact youngAdjacentOperator_basis_sameRow T a hrow
  · intro hcol
    exact youngAdjacentOperator_basis_sameCol T a hcol
  · intro hrow_ne hcol_ne
    exact ⟨youngAdjacentOperator_basis_swappable_eq T a hrow_ne hcol_ne,
      youngAdjacentOperator_basis_swappable_swap_eq T a hrow_ne hcol_ne,
      youngAdjacentCoeff_sq_sum_of_swappable T a hrow_ne hcol_ne,
      youngAdjacentOperator_swappable_eigen_plus T a hrow_ne hcol_ne,
      youngAdjacentOperator_swappable_eigen_minus T a hrow_ne hcol_ne⟩

/-- Lemma 5.1, eigenline-strengthened swappable block statement.  In the
genuine two-tableau case the off-diagonal coefficient is nonzero, and the
displayed `+1` and `-1` eigenvectors are nonzero. -/
theorem S05_Lem5_01_youngAdjacent_swappable_eigenlines {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) :
    ∀ hrow_ne : ¬ adjacentSameRow T a,
      ∀ hcol_ne : ¬ adjacentSameCol T a,
        youngAdjacentDiagCoeff T a ^ 2 < 1 ∧
        0 < youngAdjacentOffCoeff T a ∧
        youngAdjacentOffCoeff T a ≠ 0 ∧
        youngAdjacentOperator a
            (fun S =>
              youngAdjacentOffCoeff T a * tableauBasisVec T S +
                (1 - youngAdjacentDiagCoeff T a) *
                  tableauBasisVec
                    (adjacentSwapTableau T a hrow_ne hcol_ne) S) =
          (fun S =>
            youngAdjacentOffCoeff T a * tableauBasisVec T S +
              (1 - youngAdjacentDiagCoeff T a) *
                tableauBasisVec
                  (adjacentSwapTableau T a hrow_ne hcol_ne) S) ∧
        (fun S =>
              youngAdjacentOffCoeff T a * tableauBasisVec T S +
                (1 - youngAdjacentDiagCoeff T a) *
                  tableauBasisVec
                    (adjacentSwapTableau T a hrow_ne hcol_ne) S)
          ≠ (0 : TableauSpace lam) ∧
        youngAdjacentOperator a
            (fun S =>
              youngAdjacentOffCoeff T a * tableauBasisVec T S -
                (1 + youngAdjacentDiagCoeff T a) *
                  tableauBasisVec
                    (adjacentSwapTableau T a hrow_ne hcol_ne) S) =
          (fun S =>
            - (youngAdjacentOffCoeff T a * tableauBasisVec T S -
                (1 + youngAdjacentDiagCoeff T a) *
                  tableauBasisVec
                    (adjacentSwapTableau T a hrow_ne hcol_ne) S)) ∧
        (fun S =>
              youngAdjacentOffCoeff T a * tableauBasisVec T S -
                (1 + youngAdjacentDiagCoeff T a) *
                  tableauBasisVec
                    (adjacentSwapTableau T a hrow_ne hcol_ne) S)
          ≠ (0 : TableauSpace lam) := by
  intro hrow_ne hcol_ne
  exact ⟨
    youngAdjacentDiagCoeff_sq_lt_one_of_swappable T a hrow_ne hcol_ne,
    youngAdjacentOffCoeff_pos_of_swappable T a hrow_ne hcol_ne,
    youngAdjacentOffCoeff_ne_zero_of_swappable T a hrow_ne hcol_ne,
    youngAdjacentOperator_swappable_eigen_plus T a hrow_ne hcol_ne,
    youngAdjacentOperator_swappable_eigen_plus_ne_zero T a hrow_ne hcol_ne,
    youngAdjacentOperator_swappable_eigen_minus T a hrow_ne hcol_ne,
    youngAdjacentOperator_swappable_eigen_minus_ne_zero T a hrow_ne hcol_ne⟩

/-- Lemma 5.1 involution component: in the same-row case, the adjacent
operator squares to the identity on a tableau basis vector. -/
theorem S05_Lem5_01_youngAdjacentOperator_sq_basis_sameRow {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow : adjacentSameRow T a) :
    youngAdjacentOperator a
        (youngAdjacentOperator a (tableauBasisVec T)) =
      tableauBasisVec T := by
  exact youngAdjacentOperator_sq_basis_sameRow T a hrow

/-- Lemma 5.1 involution component: in the same-column case, the adjacent
operator squares to the identity on a tableau basis vector. -/
theorem S05_Lem5_01_youngAdjacentOperator_sq_basis_sameCol {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol : adjacentSameCol T a) :
    youngAdjacentOperator a
        (youngAdjacentOperator a (tableauBasisVec T)) =
      tableauBasisVec T := by
  exact youngAdjacentOperator_sq_basis_sameCol T a hcol

/-- Lemma 5.1 involution component: in the swappable case, the adjacent
operator squares to the identity on a tableau basis vector. -/
theorem S05_Lem5_01_youngAdjacentOperator_sq_basis_swappable {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentOperator a
        (youngAdjacentOperator a (tableauBasisVec T)) =
      tableauBasisVec T := by
  exact youngAdjacentOperator_sq_basis_swappable T a hrow_ne hcol_ne

/-- Lemma 5.1 involution component: the adjacent operator squares to the
identity on every tableau basis vector. -/
theorem S05_Lem5_01_youngAdjacentOperator_sq_basis {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) :
    youngAdjacentOperator a
        (youngAdjacentOperator a (tableauBasisVec T)) =
      tableauBasisVec T := by
  exact youngAdjacentOperator_sq_basis T a

/-- Lemma 5.1 Coxeter component: the adjacent operator is an involution on the
whole tableau coordinate space. -/
theorem S05_Lem5_01_youngAdjacentOperator_sq {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (a : Fin n) (f : TableauSpace lam) :
    youngAdjacentOperator a (youngAdjacentOperator a f) = f := by
  exact youngAdjacentOperator_sq a f

/-- Lemma 5.1 Coxeter-frontier component: in the fully swappable case,
distant adjacent operators commute on a tableau basis vector. -/
theorem S05_Lem5_01_youngAdjacentOperator_comm_basis_swappable_of_disjoint_indices
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
  exact youngAdjacentOperator_comm_basis_swappable_of_disjoint_indices
    T a b hdisj hrow_a hcol_a hrow_b hcol_b

/-- Lemma 5.1 Coxeter-frontier component: if the left adjacent pair is in one
row, the distant adjacent operators commute on a tableau basis vector. -/
theorem S05_Lem5_01_youngAdjacentOperator_comm_basis_left_sameRow
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hdisj : adjacentIndexDisjoint a b)
    (hrow_a : adjacentSameRow T a) :
    youngAdjacentOperator a
        (youngAdjacentOperator b (tableauBasisVec T)) =
      youngAdjacentOperator b
        (youngAdjacentOperator a (tableauBasisVec T)) := by
  exact youngAdjacentOperator_comm_basis_left_sameRow_of_disjoint_indices
    T a b hdisj hrow_a

/-- Lemma 5.1 Coxeter-frontier component: if the left adjacent pair is in one
column, the distant adjacent operators commute on a tableau basis vector. -/
theorem S05_Lem5_01_youngAdjacentOperator_comm_basis_left_sameCol
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hdisj : adjacentIndexDisjoint a b)
    (hcol_a : adjacentSameCol T a) :
    youngAdjacentOperator a
        (youngAdjacentOperator b (tableauBasisVec T)) =
      youngAdjacentOperator b
        (youngAdjacentOperator a (tableauBasisVec T)) := by
  exact youngAdjacentOperator_comm_basis_left_sameCol_of_disjoint_indices
    T a b hdisj hcol_a

/-- Lemma 5.1 Coxeter-frontier component: distant adjacent operators commute
on every tableau basis vector. -/
theorem S05_Lem5_01_youngAdjacentOperator_comm_basis_of_disjoint_indices
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hdisj : adjacentIndexDisjoint a b) :
    youngAdjacentOperator a
        (youngAdjacentOperator b (tableauBasisVec T)) =
      youngAdjacentOperator b
        (youngAdjacentOperator a (tableauBasisVec T)) := by
  exact youngAdjacentOperator_comm_basis_of_disjoint_indices T a b hdisj

/-- Lemma 5.1 Coxeter-frontier component: distant adjacent operators commute
on the whole tableau coordinate space. -/
theorem S05_Lem5_01_youngAdjacentOperator_comm_of_disjoint_indices
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (a b : Fin n) (hdisj : adjacentIndexDisjoint a b)
    (f : TableauSpace lam) :
    youngAdjacentOperator a (youngAdjacentOperator b f) =
      youngAdjacentOperator b (youngAdjacentOperator a f) := by
  exact youngAdjacentOperator_comm_of_disjoint_indices a b hdisj f

/-- Lemma 5.1 Coxeter component: consecutive adjacent operators satisfy the
braid relation on every tableau basis vector. -/
theorem S05_Lem5_01_youngAdjacentOperator_braid_basis_of_succ
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a b : Fin n)
    (hsucc : (b : Nat) = (a : Nat) + 1) :
    youngAdjacentOperator a
        (youngAdjacentOperator b
          (youngAdjacentOperator a (tableauBasisVec T))) =
      youngAdjacentOperator b
        (youngAdjacentOperator a
          (youngAdjacentOperator b (tableauBasisVec T))) := by
  exact youngAdjacentOperator_braid_basis_of_succ T a b hsucc

/-- Lemma 5.1 Coxeter component: consecutive adjacent operators satisfy the
braid relation on scalar multiples of tableau basis vectors. -/
theorem S05_Lem5_01_youngAdjacentOperator_braid_smul_basis_of_succ
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
  exact youngAdjacentOperator_braid_smul_basis_of_succ T a b hsucc c

/-- Lemma 5.1 Coxeter component: consecutive adjacent operators satisfy the
braid relation on the whole tableau coordinate space. -/
theorem S05_Lem5_01_youngAdjacentOperator_braid_of_succ
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (a b : Fin n) (hsucc : (b : Nat) = (a : Nat) + 1)
    (f : TableauSpace lam) :
    youngAdjacentOperator a
        (youngAdjacentOperator b (youngAdjacentOperator a f)) =
      youngAdjacentOperator b
        (youngAdjacentOperator a (youngAdjacentOperator b f)) := by
  exact youngAdjacentOperator_braid_of_succ a b hsucc f

/-- Lemma 5.1, bundled Coxeter relations for the concrete Young adjacent
operators on tableau coordinates: involution, distant commutation, and braid. -/
theorem S05_Lem5_01_youngAdjacent_coxeter_relations
    {n : Nat} {lam : YoungDiagram (n + 1)} :
    (∀ (a : Fin n) (f : TableauSpace lam),
      youngAdjacentOperator a (youngAdjacentOperator a f) = f) ∧
    (∀ (a b : Fin n), adjacentIndexDisjoint a b →
      ∀ f : TableauSpace lam,
        youngAdjacentOperator a (youngAdjacentOperator b f) =
          youngAdjacentOperator b (youngAdjacentOperator a f)) ∧
    (∀ (a b : Fin n), (b : Nat) = (a : Nat) + 1 →
      ∀ f : TableauSpace lam,
        youngAdjacentOperator a
            (youngAdjacentOperator b (youngAdjacentOperator a f)) =
          youngAdjacentOperator b
            (youngAdjacentOperator a (youngAdjacentOperator b f))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a f
    exact youngAdjacentOperator_sq a f
  · intro a b hdisj f
    exact youngAdjacentOperator_comm_of_disjoint_indices a b hdisj f
  · intro a b hsucc f
    exact youngAdjacentOperator_braid_of_succ a b hsucc f

/-- Lemma 5.1 action-model component: the concrete adjacent operators form a
Young adjacent Coxeter-generator action model on tableau coordinates. -/
def S05_Lem5_01_youngAdjacentActionModel {n : Nat}
    (lam : YoungDiagram (n + 1)) :
    YoungAdjacentActionModel lam :=
  youngAdjacentActionModel lam

@[simp] theorem S05_Lem5_01_youngAdjacentActionModel_op {n : Nat}
    (lam : YoungDiagram (n + 1)) :
    (S05_Lem5_01_youngAdjacentActionModel lam).op =
      youngAdjacentOperator := rfl

/-- Lemma 5.1 word-action component: a one-letter adjacent word acts by the
corresponding adjacent operator. -/
theorem S05_Lem5_01_youngAdjacentWordOperator_singleton {n : Nat}
    {lam : YoungDiagram (n + 1)} (i : Fin n) :
    youngAdjacentWordOperator (lam := lam) [i] =
      youngAdjacentOperator i := by
  funext f
  rfl

/-- Lemma 5.1 word-action component: the Young adjacent word action respects
the Coxeter equivalence generated by cancellation, distant commutation, and
braid moves. -/
theorem S05_Lem5_01_youngAdjacentWordOperator_respects_coxeter_equiv
    {n : Nat} {lam : YoungDiagram (n + 1)}
    {w w' : AdjacentWord n}
    (h : AdjacentWord.CoxeterEquiv w w') :
    youngAdjacentWordOperator (lam := lam) w =
      youngAdjacentWordOperator (lam := lam) w' := by
  exact youngAdjacentWordOperator_respects_coxeter_equiv (lam := lam) h

/-- Lemma 5.1 permutation-shadow component: a one-letter adjacent word maps to
the corresponding adjacent transposition of `Fin (n+1)`. -/
theorem S05_Lem5_01_adjacentWordPerm_singleton {n : Nat}
    (i : Fin n) :
    adjacentWordPerm [i] = adjacentSwapPerm i := by
  simp [adjacentWordPerm]

/-- Lemma 5.1 permutation-shadow component: the adjacent-word permutation map
respects the same Coxeter equivalence. -/
theorem S05_Lem5_01_adjacentWordPerm_respects_coxeter_equiv
    {n : Nat} {w w' : AdjacentWord n}
    (h : AdjacentWord.CoxeterEquiv w w') :
    adjacentWordPerm w = adjacentWordPerm w' := by
  exact adjacentWordPerm_respects_coxeter_equiv h

/-- Lemma 5.1 Coxeter-class component: the Young adjacent word action descends
to the Coxeter-word quotient. -/
theorem S05_Lem5_01_youngAdjacentCoxeterClassOperator_mk
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (w : AdjacentWord n) :
    youngAdjacentCoxeterClassOperator (lam := lam)
        (AdjacentCoxeterClass.mk w) =
      youngAdjacentWordOperator (lam := lam) w := by
  rfl

/-- Lemma 5.1 Coxeter-class component: the adjacent-word permutation shadow also
descends to the Coxeter-word quotient. -/
theorem S05_Lem5_01_adjacentCoxeterClassPerm_mk
    {n : Nat} (w : AdjacentWord n) :
    adjacentCoxeterClassPerm (AdjacentCoxeterClass.mk w) =
      adjacentWordPerm w := by
  rfl

/-- Strongest assumption-free Lemma 5.1 package currently formalized: the concrete
Young adjacent operators are the generators of a Coxeter action model, their
word action is invariant under Coxeter moves, and the same moves preserve the
underlying adjacent-transposition word in `Perm (Fin (n+1))`.

This theorem intentionally stops short of identifying the model with the
classical Specht module. -/
theorem S05_Lem5_01_adjacentTranspositionsInYoungsBasis_coxeterModel
    {n : Nat} {lam : YoungDiagram (n + 1)} :
    (S05_Lem5_01_youngAdjacentActionModel lam).op =
        youngAdjacentOperator ∧
    (∀ (a : Fin n) (f : TableauSpace lam),
      youngAdjacentOperator a (youngAdjacentOperator a f) = f) ∧
    (∀ (a b : Fin n), adjacentIndexDisjoint a b →
      ∀ f : TableauSpace lam,
        youngAdjacentOperator a (youngAdjacentOperator b f) =
          youngAdjacentOperator b (youngAdjacentOperator a f)) ∧
    (∀ (a b : Fin n), (b : Nat) = (a : Nat) + 1 →
      ∀ f : TableauSpace lam,
        youngAdjacentOperator a
            (youngAdjacentOperator b (youngAdjacentOperator a f)) =
          youngAdjacentOperator b
            (youngAdjacentOperator a (youngAdjacentOperator b f))) ∧
    (∀ {w w' : AdjacentWord n}, AdjacentWord.CoxeterEquiv w w' →
      youngAdjacentWordOperator (lam := lam) w =
        youngAdjacentWordOperator (lam := lam) w') ∧
    (∀ {w w' : AdjacentWord n}, AdjacentWord.CoxeterEquiv w w' →
      adjacentWordPerm w = adjacentWordPerm w') ∧
    (∀ w : AdjacentWord n,
      youngAdjacentCoxeterClassOperator (lam := lam)
          (AdjacentCoxeterClass.mk w) =
        youngAdjacentWordOperator (lam := lam) w) ∧
    (∀ w : AdjacentWord n,
      adjacentCoxeterClassPerm (AdjacentCoxeterClass.mk w) =
        adjacentWordPerm w) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a f
    exact youngAdjacentOperator_sq a f
  · intro a b hdisj f
    exact youngAdjacentOperator_comm_of_disjoint_indices a b hdisj f
  · intro a b hsucc f
    exact youngAdjacentOperator_braid_of_succ a b hsucc f
  · intro w w' h
    exact youngAdjacentWordOperator_respects_coxeter_equiv (lam := lam) h
  · intro w w' h
    exact adjacentWordPerm_respects_coxeter_equiv h
  · intro w
    rfl
  · intro w
    rfl

end DictatorshipTesting
