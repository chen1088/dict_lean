import DictatorshipTesting.Paper.S05_Lem5_01_AdjacentTranspositionsInYoungsBasis
import DictatorshipTesting.Paper.Defs.S05_IntDef_YoungOrthogonalActionData

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S05_Lem5_02_TypeAAdjacentWordPresentation`
- `DictatorshipTesting.Paper.S05_Thm5_03_YoungOrthogonalAction`
-/

/-!
The type-A Coxeter presentation needed to turn the adjacent Young operators
from Lemma 5.1 into an action of the full symmetric group.  The proof uses an
explicit parabolic normal form: a word on `Fin (n + 1)` is Coxeter-equivalent
to an ascending segment ending in the top generator, followed by a lifted word
on `Fin n`.
-/

noncomputable section

namespace DictatorshipTesting

namespace AdjacentWord

/-- One Coxeter step generates a Coxeter equivalence. -/
theorem coxeterEquiv_of_step {n : Nat} {w v : AdjacentWord n}
    (h : CoxeterStep w v) : CoxeterEquiv w v :=
  Relation.EqvGen.rel w v h

/-- Coxeter equivalence is preserved by a common letter on the left. -/
theorem coxeterEquiv_cons {n : Nat} (i : Fin n)
    {w v : AdjacentWord n} (h : CoxeterEquiv w v) :
    CoxeterEquiv (i :: w) (i :: v) := by
  induction h with
  | rel w v hstep =>
      exact coxeterEquiv_of_step (CoxeterStep.context_cons i hstep)
  | refl w => exact Relation.EqvGen.refl _
  | symm w v _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans w v u _ _ ihwv ihvu => exact Relation.EqvGen.trans _ _ _ ihwv ihvu

/-- Coxeter equivalence is preserved by a common word on the left. -/
theorem coxeterEquiv_append_left {n : Nat} (u : AdjacentWord n)
    {w v : AdjacentWord n} (h : CoxeterEquiv w v) :
    CoxeterEquiv (u ++ w) (u ++ v) := by
  induction u with
  | nil => simpa using h
  | cons i u ih =>
      simpa only [List.cons_append] using coxeterEquiv_cons i ih

/-- One Coxeter step remains a step after appending a common right context. -/
theorem coxeterStep_append_right {n : Nat} {w v : AdjacentWord n}
    (h : CoxeterStep w v) (u : AdjacentWord n) :
    CoxeterStep (w ++ u) (v ++ u) := by
  induction h with
  | cancel_pair i w =>
      simpa only [List.cons_append] using CoxeterStep.cancel_pair i (w ++ u)
  | swap_disjoint i j w hdisj =>
      simpa only [List.cons_append] using
        CoxeterStep.swap_disjoint i j (w ++ u) hdisj
  | braid i j w hsucc =>
      simpa only [List.cons_append] using CoxeterStep.braid i j (w ++ u) hsucc
  | context_cons i h ih =>
      simpa only [List.cons_append] using CoxeterStep.context_cons i ih

/-- Coxeter equivalence is preserved by a common word on the right. -/
theorem coxeterEquiv_append_right {n : Nat} {w v : AdjacentWord n}
    (h : CoxeterEquiv w v) (u : AdjacentWord n) :
    CoxeterEquiv (w ++ u) (v ++ u) := by
  induction h with
  | rel w v hstep =>
      exact coxeterEquiv_of_step (coxeterStep_append_right hstep u)
  | refl w => exact Relation.EqvGen.refl _
  | symm w v _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans w v z _ _ ihwv ihvz => exact Relation.EqvGen.trans _ _ _ ihwv ihvz

end AdjacentWord

/-- The ascending adjacent word `[start, start+1, ..., rank-1]`. -/
def adjacentAscendingSegment (rank start : Nat) : AdjacentWord rank :=
  if h : start < rank then
    (⟨start, h⟩ : Fin rank) :: adjacentAscendingSegment rank (start + 1)
  else
    []
termination_by rank - start
decreasing_by omega

@[simp] theorem adjacentAscendingSegment_of_lt {rank start : Nat}
    (h : start < rank) :
    adjacentAscendingSegment rank start =
      (⟨start, h⟩ : Fin rank) :: adjacentAscendingSegment rank (start + 1) := by
  rw [adjacentAscendingSegment]
  simp [h]

@[simp] theorem adjacentAscendingSegment_of_le {rank start : Nat}
    (h : rank ≤ start) : adjacentAscendingSegment rank start = [] := by
  rw [adjacentAscendingSegment]
  simp [Nat.not_lt.mpr h]

/-- Embed a lower-rank adjacent word by keeping every generator index. -/
def liftAdjacentWord {n : Nat} (w : AdjacentWord n) : AdjacentWord (n + 1) :=
  w.map Fin.castSucc

@[simp] theorem liftAdjacentWord_nil {n : Nat} :
    liftAdjacentWord ([] : AdjacentWord n) = [] := rfl

@[simp] theorem liftAdjacentWord_cons {n : Nat} (i : Fin n) (w : AdjacentWord n) :
    liftAdjacentWord (i :: w) = i.castSucc :: liftAdjacentWord w := rfl

@[simp] theorem liftAdjacentWord_append {n : Nat} (w v : AdjacentWord n) :
    liftAdjacentWord (w ++ v) = liftAdjacentWord w ++ liftAdjacentWord v := by
  simp [liftAdjacentWord]

/-- Lifting generator indices preserves one elementary Coxeter move. -/
theorem liftAdjacentWord_coxeterStep {n : Nat} {w v : AdjacentWord n}
    (h : AdjacentWord.CoxeterStep w v) :
    AdjacentWord.CoxeterStep (liftAdjacentWord w) (liftAdjacentWord v) := by
  induction h with
  | cancel_pair i w =>
      exact AdjacentWord.CoxeterStep.cancel_pair i.castSucc (liftAdjacentWord w)
  | swap_disjoint i j w hdisj =>
      exact AdjacentWord.CoxeterStep.swap_disjoint i.castSucc j.castSucc
        (liftAdjacentWord w) hdisj
  | braid i j w hsucc =>
      exact AdjacentWord.CoxeterStep.braid i.castSucc j.castSucc
        (liftAdjacentWord w) hsucc
  | context_cons i h ih =>
      exact AdjacentWord.CoxeterStep.context_cons i.castSucc ih

/-- Lifting generator indices preserves Coxeter equivalence. -/
theorem liftAdjacentWord_coxeterEquiv {n : Nat} {w v : AdjacentWord n}
    (h : AdjacentWord.CoxeterEquiv w v) :
    AdjacentWord.CoxeterEquiv (liftAdjacentWord w) (liftAdjacentWord v) := by
  induction h with
  | rel w v hstep =>
      exact AdjacentWord.coxeterEquiv_of_step
        (liftAdjacentWord_coxeterStep hstep)
  | refl w => exact Relation.EqvGen.refl _
  | symm w v _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans w v u _ _ ihwv ihvu => exact Relation.EqvGen.trans _ _ _ ihwv ihvu

theorem castSucc_adjacentEntryLo {n : Nat} (i : Fin n) :
    Fin.castSucc (adjacentEntryLo i) = adjacentEntryLo i.castSucc := rfl

theorem castSucc_adjacentEntryHi {n : Nat} (i : Fin n) :
    Fin.castSucc (adjacentEntryHi i) = adjacentEntryHi i.castSucc := by
  apply Fin.ext
  simp [adjacentEntryHi]

/-- An earlier adjacent swap commutes with embedding into a larger `Fin`. -/
theorem adjacentSwapValue_castSucc {n : Nat} (i : Fin n) (x : Fin (n + 1)) :
    Fin.castSucc (adjacentSwapValue i x) =
      adjacentSwapValue i.castSucc x.castSucc := by
  by_cases hlo : x = adjacentEntryLo i
  · subst x
    rw [adjacentSwapValue_lo, castSucc_adjacentEntryHi,
      castSucc_adjacentEntryLo, adjacentSwapValue_lo]
  · by_cases hhi : x = adjacentEntryHi i
    · subst x
      rw [adjacentSwapValue_hi, castSucc_adjacentEntryLo,
        castSucc_adjacentEntryHi, adjacentSwapValue_hi]
    · have hlo' : x.castSucc ≠ adjacentEntryLo i.castSucc := by
        intro h
        apply hlo
        apply Fin.ext
        simpa [adjacentEntryLo] using congrArg Fin.val h
      have hhi' : x.castSucc ≠ adjacentEntryHi i.castSucc := by
        intro h
        apply hhi
        apply Fin.ext
        simpa [adjacentEntryHi] using congrArg Fin.val h
      rw [adjacentSwapValue_of_ne_lo_hi i hlo hhi,
        adjacentSwapValue_of_ne_lo_hi i.castSucc hlo' hhi']

/-- An embedded adjacent swap fixes the new largest coordinate. -/
theorem adjacentSwapValue_castSucc_last {n : Nat} (i : Fin n) :
    adjacentSwapValue i.castSucc (Fin.last (n + 1)) = Fin.last (n + 1) := by
  apply adjacentSwapValue_of_ne_lo_hi
  · intro h
    have hv := congrArg Fin.val h
    simp [adjacentEntryLo] at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    simp [adjacentEntryHi] at hv
    omega

/-- The permutation of a lifted word restricts to the original permutation. -/
theorem adjacentWordPerm_lift_apply_castSucc {n : Nat}
    (w : AdjacentWord n) (x : Fin (n + 1)) :
    adjacentWordPerm (liftAdjacentWord w) x.castSucc =
      (adjacentWordPerm w x).castSucc := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      simp only [liftAdjacentWord_cons, adjacentWordPerm_cons_apply]
      rw [ih, ← adjacentSwapValue_castSucc]

/-- The permutation of a lifted word fixes the new largest coordinate. -/
theorem adjacentWordPerm_lift_last {n : Nat} (w : AdjacentWord n) :
    adjacentWordPerm (liftAdjacentWord w) (Fin.last (n + 1)) =
      Fin.last (n + 1) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      simp only [liftAdjacentWord_cons, adjacentWordPerm_cons_apply, ih]
      exact adjacentSwapValue_castSucc_last i

/-- Equality of lifted permutation shadows reflects equality at lower rank. -/
theorem adjacentWordPerm_lift_injective {n : Nat} {w v : AdjacentWord n}
    (h : adjacentWordPerm (liftAdjacentWord w) =
      adjacentWordPerm (liftAdjacentWord v)) :
    adjacentWordPerm w = adjacentWordPerm v := by
  apply Equiv.ext
  intro x
  have hx := Equiv.congr_fun h x.castSucc
  rw [adjacentWordPerm_lift_apply_castSucc,
    adjacentWordPerm_lift_apply_castSucc] at hx
  exact Fin.castSucc_injective _ hx

/-- A generator strictly below an ascending segment commutes through the whole
segment and emerges on the right. -/
theorem adjacent_cons_ascendingSegment_commute_right
    {rank start : Nat} (i : Fin rank) (hsep : (i : Nat) + 1 < start) :
    AdjacentWord.CoxeterEquiv
      (i :: adjacentAscendingSegment rank start)
      (adjacentAscendingSegment rank start ++ [i]) := by
  by_cases hstart : start < rank
  · rw [adjacentAscendingSegment_of_lt hstart]
    let j : Fin rank := ⟨start, hstart⟩
    have hdisj : adjacentIndexDisjoint i j := Or.inl hsep
    have hswap : AdjacentWord.CoxeterEquiv
        (i :: j :: adjacentAscendingSegment rank (start + 1))
        (j :: i :: adjacentAscendingSegment rank (start + 1)) :=
      AdjacentWord.coxeterEquiv_of_step
        (AdjacentWord.CoxeterStep.swap_disjoint i j
          (adjacentAscendingSegment rank (start + 1)) hdisj)
    have ih := adjacent_cons_ascendingSegment_commute_right
      (start := start + 1) i (by omega)
    exact Relation.EqvGen.trans _ _ _ hswap (by
      simpa only [List.cons_append] using AdjacentWord.coxeterEquiv_cons j ih)
  · rw [adjacentAscendingSegment_of_le (Nat.le_of_not_gt hstart)]
    exact Relation.EqvGen.refl _
termination_by rank - start
decreasing_by omega

/-- A generator occurring strictly inside an ascending segment crosses it by
the braid relation and emerges one index lower on the right. -/
theorem adjacent_cons_ascendingSegment_inside
    {rank start : Nat} (i : Fin rank) (hinside : start < (i : Nat)) :
    AdjacentWord.CoxeterEquiv
      (i :: adjacentAscendingSegment rank start)
      (adjacentAscendingSegment rank start ++
        [⟨(i : Nat) - 1, by omega⟩]) := by
  have hstart : start < rank := lt_trans hinside i.isLt
  rw [adjacentAscendingSegment_of_lt hstart]
  let j : Fin rank := ⟨start, hstart⟩
  by_cases hfar : start + 1 < (i : Nat)
  · have hdisj : adjacentIndexDisjoint i j := Or.inr hfar
    have hswap : AdjacentWord.CoxeterEquiv
        (i :: j :: adjacentAscendingSegment rank (start + 1))
        (j :: i :: adjacentAscendingSegment rank (start + 1)) :=
      AdjacentWord.coxeterEquiv_of_step
        (AdjacentWord.CoxeterStep.swap_disjoint i j
          (adjacentAscendingSegment rank (start + 1)) hdisj)
    have ih := adjacent_cons_ascendingSegment_inside
      (start := start + 1) i hfar
    exact Relation.EqvGen.trans _ _ _ hswap (by
      simpa only [List.cons_append] using AdjacentWord.coxeterEquiv_cons j ih)
  · have hi : (i : Nat) = start + 1 := by omega
    have hiLt : start + 1 < rank := by omega
    rw [adjacentAscendingSegment_of_lt hiLt]
    let i' : Fin rank := ⟨start + 1, hiLt⟩
    have hij : i = i' := Fin.ext hi
    subst i
    have hbraidForward : AdjacentWord.CoxeterEquiv
        (j :: i' :: j :: adjacentAscendingSegment rank (start + 2))
        (i' :: j :: i' :: adjacentAscendingSegment rank (start + 2)) :=
      AdjacentWord.coxeterEquiv_of_step
        (AdjacentWord.CoxeterStep.braid j i'
          (adjacentAscendingSegment rank (start + 2)) (by rfl))
    have hbraid := Relation.EqvGen.symm _ _ hbraidForward
    have hcommute := adjacent_cons_ascendingSegment_commute_right
      (start := start + 2) j (by
        change start + 1 < start + 2
        omega)
    have hcontext := AdjacentWord.coxeterEquiv_append_left [j, i'] hcommute
    exact Relation.EqvGen.trans _ _ _ hbraid (by
      simpa [i', j, Nat.add_assoc] using hcontext)
termination_by (i : Nat) - start
decreasing_by omega

/-- Multiplying a top-segment normal form by one adjacent generator produces
another top-segment normal form and at most one lower-rank generator. -/
theorem adjacent_cons_ascendingSegment_normalForm {n : Nat}
    (i : Fin (n + 1)) (k : Fin (n + 2)) :
    ∃ k' : Fin (n + 2), ∃ u : AdjacentWord n,
      AdjacentWord.CoxeterEquiv
        (i :: adjacentAscendingSegment (n + 1) (k : Nat))
        (adjacentAscendingSegment (n + 1) (k' : Nat) ++
          liftAdjacentWord u) := by
  by_cases hbelow : (i : Nat) + 1 < (k : Nat)
  · let ilow : Fin n := ⟨i, by omega⟩
    refine ⟨k, [ilow], ?_⟩
    have h := adjacent_cons_ascendingSegment_commute_right i hbelow
    have hilow : ilow.castSucc = i := Fin.ext rfl
    simpa only [liftAdjacentWord_cons, liftAdjacentWord_nil, hilow] using h
  · by_cases hextend : (i : Nat) + 1 = (k : Nat)
    · let k' : Fin (n + 2) := ⟨i, by omega⟩
      refine ⟨k', [], ?_⟩
      simp only [liftAdjacentWord_nil, List.append_nil]
      rw [adjacentAscendingSegment_of_lt i.isLt]
      have hk : k = (⟨(i : Nat) + 1, by omega⟩ : Fin (n + 2)) :=
        Fin.ext hextend.symm
      rw [hk]
      exact Relation.EqvGen.refl _
    · by_cases heq : (i : Nat) = (k : Nat)
      · have hklt : (k : Nat) < n + 1 := by omega
        let k' : Fin (n + 2) := ⟨(k : Nat) + 1, by omega⟩
        refine ⟨k', [], ?_⟩
        simp only [liftAdjacentWord_nil, List.append_nil]
        rw [adjacentAscendingSegment_of_lt hklt]
        have hik : i = (⟨k, hklt⟩ : Fin (n + 1)) := Fin.ext heq
        subst i
        exact AdjacentWord.coxeterEquiv_of_step
          (AdjacentWord.CoxeterStep.cancel_pair
            (⟨k, hklt⟩ : Fin (n + 1))
            (adjacentAscendingSegment (n + 1) ((k : Nat) + 1)))
      · have hins : (k : Nat) < (i : Nat) := by omega
        let ilow : Fin n := ⟨(i : Nat) - 1, by omega⟩
        refine ⟨k, [ilow], ?_⟩
        have h := adjacent_cons_ascendingSegment_inside i hins
        have hilow : ilow.castSucc =
            (⟨(i : Nat) - 1, by omega⟩ : Fin (n + 1)) := Fin.ext rfl
        simpa only [liftAdjacentWord_cons, liftAdjacentWord_nil, hilow] using h

/-- Every word has a parabolic normal form consisting of one ascending segment
ending in the top generator and one lifted lower-rank word. -/
theorem exists_ascendingSegment_lift_normalForm {n : Nat}
    (w : AdjacentWord (n + 1)) :
    ∃ k : Fin (n + 2), ∃ v : AdjacentWord n,
      AdjacentWord.CoxeterEquiv w
        (adjacentAscendingSegment (n + 1) (k : Nat) ++
          liftAdjacentWord v) := by
  induction w with
  | nil =>
      let k : Fin (n + 2) := Fin.last (n + 1)
      refine ⟨k, [], ?_⟩
      rw [adjacentAscendingSegment_of_le (by simp [k])]
      exact Relation.EqvGen.refl _
  | cons i w ih =>
      rcases ih with ⟨k, v, hw⟩
      rcases adjacent_cons_ascendingSegment_normalForm i k with ⟨k', u, hi⟩
      refine ⟨k', u ++ v, ?_⟩
      have hprefix := AdjacentWord.coxeterEquiv_cons i hw
      have hrewrite := AdjacentWord.coxeterEquiv_append_right hi (liftAdjacentWord v)
      have hrewrite' : AdjacentWord.CoxeterEquiv
          (i :: (adjacentAscendingSegment (n + 1) (k : Nat) ++
            liftAdjacentWord v))
          (adjacentAscendingSegment (n + 1) (k' : Nat) ++
            liftAdjacentWord (u ++ v)) := by
        simpa only [List.cons_append, List.append_assoc,
          liftAdjacentWord_append] using hrewrite
      exact Relation.EqvGen.trans _ _ _ hprefix hrewrite'

/-- The ascending segment beginning at `start` sends the largest coordinate to
`start`. -/
theorem adjacentWordPerm_ascendingSegment_last
    {rank start : Nat} (hstart : start ≤ rank) :
    adjacentWordPerm (adjacentAscendingSegment rank start) (Fin.last rank) =
      (⟨start, by omega⟩ : Fin (rank + 1)) := by
  by_cases hlt : start < rank
  · rw [adjacentAscendingSegment_of_lt hlt, adjacentWordPerm_cons_apply]
    let i : Fin rank := ⟨start, hlt⟩
    have ih := adjacentWordPerm_ascendingSegment_last
      (rank := rank) (start := start + 1) (by omega)
    rw [ih]
    simpa [i, adjacentEntryLo, adjacentEntryHi] using adjacentSwapValue_hi i
  · have heq : start = rank := by omega
    subst start
    rw [adjacentAscendingSegment_of_le (le_refl rank)]
    rfl
termination_by rank - start
decreasing_by omega

/-- The top-segment coordinate is read off by applying a normal-form
permutation to the largest point. -/
theorem adjacentWordPerm_normalForm_last {n : Nat}
    (k : Fin (n + 2)) (v : AdjacentWord n) :
    adjacentWordPerm
        (adjacentAscendingSegment (n + 1) (k : Nat) ++ liftAdjacentWord v)
        (Fin.last (n + 1)) = k := by
  rw [adjacentWordPerm_append]
  change adjacentWordPerm (adjacentAscendingSegment (n + 1) (k : Nat))
      (adjacentWordPerm (liftAdjacentWord v) (Fin.last (n + 1))) = k
  rw [adjacentWordPerm_lift_last,
    adjacentWordPerm_ascendingSegment_last (by omega)]

/-- Completeness of the type-A Coxeter relations: two adjacent words represent
the same permutation exactly when Coxeter moves connect them. -/
theorem adjacentWordPerm_complete {n : Nat} {w v : AdjacentWord n}
    (hperm : adjacentWordPerm w = adjacentWordPerm v) :
    AdjacentWord.CoxeterEquiv w v := by
  induction n with
  | zero =>
      cases w with
      | nil =>
          cases v with
          | nil => exact Relation.EqvGen.refl _
          | cons i v => exact Fin.elim0 i
      | cons i w => exact Fin.elim0 i
  | succ n ih =>
      rcases exists_ascendingSegment_lift_normalForm w with ⟨kw, ww, hw⟩
      rcases exists_ascendingSegment_lift_normalForm v with ⟨kv, vv, hv⟩
      have hnormal :
          adjacentWordPerm
              (adjacentAscendingSegment (n + 1) (kw : Nat) ++
                liftAdjacentWord ww) =
            adjacentWordPerm
              (adjacentAscendingSegment (n + 1) (kv : Nat) ++
                liftAdjacentWord vv) :=
        (adjacentWordPerm_respects_coxeter_equiv hw).symm.trans
          (hperm.trans (adjacentWordPerm_respects_coxeter_equiv hv))
      have hk : kw = kv := by
        have hlast := Equiv.congr_fun hnormal (Fin.last (n + 1))
        simpa only [adjacentWordPerm_normalForm_last] using hlast
      subst kv
      have hlift :
          adjacentWordPerm (liftAdjacentWord ww) =
            adjacentWordPerm (liftAdjacentWord vv) := by
        rw [adjacentWordPerm_append, adjacentWordPerm_append] at hnormal
        exact mul_left_cancel hnormal
      have hlower : adjacentWordPerm ww = adjacentWordPerm vv :=
        adjacentWordPerm_lift_injective hlift
      have hlowerCoxeter : AdjacentWord.CoxeterEquiv ww vv := ih hlower
      have hmiddle := AdjacentWord.coxeterEquiv_append_left
        (adjacentAscendingSegment (n + 1) (kw : Nat))
        (liftAdjacentWord_coxeterEquiv hlowerCoxeter)
      exact Relation.EqvGen.trans _ _ _ hw
        (Relation.EqvGen.trans _ _ _ hmiddle (Relation.EqvGen.symm _ _ hv))

/-- The concrete permutation shadow of a generator is the literal adjacent
transposition used by the Section 5 interface. -/
theorem adjacentSwapPerm_eq_s05_adjacentTransposition {n : Nat} (i : Fin n) :
    adjacentSwapPerm i = s05_adjacentTransposition i := by
  ext x
  have hhi : adjacentEntryHi i = i.succ := Fin.ext rfl
  simp [adjacentSwapPerm_apply, adjacentSwapValue,
    s05_adjacentTransposition, adjacentEntryLo, hhi, Equiv.swap_apply_def]

/-- Every finite permutation is represented by an adjacent word. -/
theorem adjacentWordPerm_surjective {n : Nat} :
    Function.Surjective (@adjacentWordPerm n) := by
  intro σ
  have hmem : σ ∈ Submonoid.closure
      (Set.range fun i : Fin n => s05_adjacentTransposition i) := by
    rw [show
      (Set.range fun i : Fin n => s05_adjacentTransposition i) =
        Set.range (fun i : Fin n => Equiv.swap i.castSucc i.succ) by rfl]
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]
    trivial
  exact Submonoid.closure_induction
    (motive := fun τ _ => ∃ w : AdjacentWord n, adjacentWordPerm w = τ)
    (fun τ hτ => by
      rcases hτ with ⟨i, rfl⟩
      refine ⟨[i], ?_⟩
      simp [adjacentSwapPerm_eq_s05_adjacentTransposition])
    ⟨[], rfl⟩
    (fun τ υ _ _ hτ hυ => by
      rcases hτ with ⟨w, rfl⟩
      rcases hυ with ⟨v, rfl⟩
      exact ⟨w ++ v, adjacentWordPerm_append w v⟩)
    hmem

/-- A fixed adjacent-word representative of a permutation. -/
noncomputable def adjacentWordOfPerm {n : Nat}
    (σ : Perm (Fin (n + 1))) : AdjacentWord n :=
  Classical.choose (adjacentWordPerm_surjective σ)

@[simp] theorem adjacentWordPerm_adjacentWordOfPerm {n : Nat}
    (σ : Perm (Fin (n + 1))) :
    adjacentWordPerm (adjacentWordOfPerm σ) = σ :=
  Classical.choose_spec (adjacentWordPerm_surjective σ)

/-- The Young operator represented by a permutation, using the complete
adjacent-word presentation. -/
noncomputable def youngPermutationOperator {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (σ : Perm (Fin (n + 1))) (f : TableauSpace lam) : TableauSpace lam :=
  youngAdjacentWordOperator (adjacentWordOfPerm σ) f

/-- The permutation operator can be evaluated using any adjacent word for the
permutation, not only the fixed representative chosen in its definition. -/
theorem youngPermutationOperator_adjacentWord {n : Nat}
    {lam : YoungDiagram (n + 1)} (w : AdjacentWord n)
    (f : TableauSpace lam) :
    youngPermutationOperator (adjacentWordPerm w) f =
      youngAdjacentWordOperator w f := by
  have hperm : adjacentWordPerm (adjacentWordOfPerm (adjacentWordPerm w)) =
      adjacentWordPerm w := adjacentWordPerm_adjacentWordOfPerm _
  have hcox := adjacentWordPerm_complete hperm
  exact congrFun
    (youngAdjacentWordOperator_respects_coxeter_equiv (lam := lam) hcox) f

theorem youngAdjacentWordOperator_add {n : Nat}
    {lam : YoungDiagram (n + 1)} (w : AdjacentWord n)
    (f g : TableauSpace lam) :
    youngAdjacentWordOperator w (f + g) =
      youngAdjacentWordOperator w f + youngAdjacentWordOperator w g := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      rw [youngAdjacentWordOperator_cons, youngAdjacentWordOperator_cons,
        youngAdjacentWordOperator_cons, ih]
      change youngAdjacentOperator i
          (fun S => youngAdjacentWordOperator w f S +
            youngAdjacentWordOperator w g S) =
        fun S => youngAdjacentOperator i (youngAdjacentWordOperator w f) S +
          youngAdjacentOperator i (youngAdjacentWordOperator w g) S
      exact youngAdjacentOperator_add i
        (youngAdjacentWordOperator w f) (youngAdjacentWordOperator w g)

theorem youngAdjacentWordOperator_smul {n : Nat}
    {lam : YoungDiagram (n + 1)} (w : AdjacentWord n)
    (c : Real) (f : TableauSpace lam) :
    youngAdjacentWordOperator w (c • f) =
      c • youngAdjacentWordOperator w f := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      rw [youngAdjacentWordOperator_cons, youngAdjacentWordOperator_cons,
        ih]
      change youngAdjacentOperator i
          (fun S => c * youngAdjacentWordOperator w f S) =
        fun S => c * youngAdjacentOperator i (youngAdjacentWordOperator w f) S
      exact youngAdjacentOperator_smul i c (youngAdjacentWordOperator w f)

theorem youngPermutationOperator_add {n : Nat}
    {lam : YoungDiagram (n + 1)} (σ : Perm (Fin (n + 1)))
    (f g : TableauSpace lam) :
    youngPermutationOperator σ (f + g) =
      youngPermutationOperator σ f + youngPermutationOperator σ g := by
  exact youngAdjacentWordOperator_add (adjacentWordOfPerm σ) f g

theorem youngPermutationOperator_smul {n : Nat}
    {lam : YoungDiagram (n + 1)} (σ : Perm (Fin (n + 1)))
    (c : Real) (f : TableauSpace lam) :
    youngPermutationOperator σ (c • f) = c • youngPermutationOperator σ f := by
  exact youngAdjacentWordOperator_smul (adjacentWordOfPerm σ) c f

theorem youngPermutationOperator_one {n : Nat}
    {lam : YoungDiagram (n + 1)} (f : TableauSpace lam) :
    youngPermutationOperator (1 : Perm (Fin (n + 1))) f = f := by
  have hperm : adjacentWordPerm (adjacentWordOfPerm
      (1 : Perm (Fin (n + 1)))) = adjacentWordPerm ([] : AdjacentWord n) := by
    simp
  have hcox := adjacentWordPerm_complete hperm
  have hop := youngAdjacentWordOperator_respects_coxeter_equiv
    (lam := lam) hcox
  exact congrFun hop f

theorem youngPermutationOperator_mul {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (σ τ : Perm (Fin (n + 1))) (f : TableauSpace lam) :
    youngPermutationOperator (σ * τ) f =
      youngPermutationOperator σ (youngPermutationOperator τ f) := by
  have hperm : adjacentWordPerm (adjacentWordOfPerm (σ * τ)) =
      adjacentWordPerm (adjacentWordOfPerm σ ++ adjacentWordOfPerm τ) := by
    rw [adjacentWordPerm_adjacentWordOfPerm, adjacentWordPerm_append,
      adjacentWordPerm_adjacentWordOfPerm, adjacentWordPerm_adjacentWordOfPerm]
  have hcox := adjacentWordPerm_complete hperm
  have hop := youngAdjacentWordOperator_respects_coxeter_equiv
    (lam := lam) hcox
  change youngAdjacentWordOperator (adjacentWordOfPerm (σ * τ)) f =
    youngAdjacentWordOperator (adjacentWordOfPerm σ)
      (youngAdjacentWordOperator (adjacentWordOfPerm τ) f)
  rw [congrFun hop f, youngAdjacentWordOperator_append]

theorem youngPermutationOperator_adjacent {n : Nat}
    {lam : YoungDiagram (n + 1)} (i : Fin n) (f : TableauSpace lam) :
    youngPermutationOperator (s05_adjacentTransposition i) f =
      youngAdjacentOperator i f := by
  have hperm : adjacentWordPerm
      (adjacentWordOfPerm (s05_adjacentTransposition i)) =
      adjacentWordPerm ([i] : AdjacentWord n) := by
    rw [adjacentWordPerm_adjacentWordOfPerm]
    simp [adjacentSwapPerm_eq_s05_adjacentTransposition]
  have hcox := adjacentWordPerm_complete hperm
  have hop := youngAdjacentWordOperator_respects_coxeter_equiv
    (lam := lam) hcox
  exact congrFun hop f

/-- The concrete Young orthogonal action supplied by the type-A presentation. -/
noncomputable def youngOrthogonalActionData {n : Nat}
    (lam : YoungDiagram (n + 1)) : YoungOrthogonalActionData lam where
  rep :=
    { rho := youngPermutationOperator
      map_add := youngPermutationOperator_add
      map_smul := youngPermutationOperator_smul
      map_mul := youngPermutationOperator_mul
      map_one := youngPermutationOperator_one }
  rho_adjacent := youngPermutationOperator_adjacent

/-- Internal construction of the action asserted by Section 5.1. -/
theorem youngOrthogonalActionData_nonempty {n : Nat}
    (lam : YoungDiagram (n + 1)) : Nonempty (YoungOrthogonalActionData lam) :=
  ⟨youngOrthogonalActionData lam⟩

end DictatorshipTesting
