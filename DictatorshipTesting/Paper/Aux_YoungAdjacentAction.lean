import DictatorshipTesting.Paper.Aux_YoungOrthogonal

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S05_Lem5_01_AdjacentTranspositionsInYoungsBasis`
-/


/-!
# Young adjacent action package

This helper packages the concrete adjacent operators from
`Aux_YoungOrthogonal` as a Coxeter-generator action on tableau coordinates.
It also provides a word action and proves invariance under the elementary
Coxeter word moves already justified by the operator-level relations.

The file deliberately does not identify this model with the classical Specht
module.  That identification is a separate representation-theoretic input.
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

end DictatorshipTesting
