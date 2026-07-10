import DictatorshipTesting.Paper.Defs.S05_Def5_14_OddSignPatternMultiset
import DictatorshipTesting.Paper.Defs.S05_Def5_15_MatchingCharacters
import DictatorshipTesting.Paper.Defs.S05_Def5_25_TableauOddHeight
import DictatorshipTesting.Paper.S05_Lem5_08_TwoBoxDimensionRecursion
import DictatorshipTesting.Paper.S05_Lem5_09_OneBoxDimensionRecursion

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_11_MatchingSubgroupEigenbasis`
-/


/-!
Paper statement: Lemma 5.10 (`lem:X-size`)
Title in paper: Sizes of the sign-pattern multisets.

Status: proven. The genuine recursive even and odd label multisets are defined
in Definitions 5.13--5.14. This file proves their assumption-free `tableauDim`
cardinalities, identifies their zero and high multiplicities with `zEven`,
`hEvenTableau`, and `hOddTableau`, and connects any finite label enumeration to
those multiplicities. The older `youngDim` wrappers remain explicit alternate
statements requiring the named dimension branching inputs.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

private noncomputable def emptyStandardYoungTableau
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

private theorem tableauDimNat_zero (lam : YoungDiagram 0) :
    tableauDimNat lam = 1 := by
  rw [tableauDimNat, Fintype.card_eq_one_iff]
  refine ⟨emptyStandardYoungTableau lam, ?_⟩
  intro T
  apply standardYoungTableau_ext_entry
  intro u
  exact Fin.elim0 u.1.1

/-- The genuine even sign-pattern multiset has one label for every standard
tableau, with multiplicity. -/
theorem S05_Lem5_10_evenSignPatternMultiset_card :
    forall (m : Nat) (lam : YoungDiagram (2 * m)),
      ((S05_evenSignPatternMultiset m lam).card : Real) = tableauDim lam := by
  intro m
  induction m with
  | zero =>
      intro lam
      simp [S05_evenSignPatternMultiset, tableauDim, tableauDimNat_zero]
  | succ m ih =>
      intro lam
      calc
        ((S05_evenSignPatternMultiset (m + 1) lam).card : Real) =
            (horizontalTwoStripChildrenEven (m + 1) lam).sum
                (fun mu => ((S05_evenSignPatternMultiset m mu).card : Real)) +
              (verticalTwoStripChildrenEven (m + 1) lam).sum
                (fun mu => ((S05_evenSignPatternMultiset m mu).card : Real)) := by
          simp [S05_evenSignPatternMultiset]
        _ =
            (horizontalTwoStripChildrenEven (m + 1) lam).sum
                (fun mu => tableauDim mu) +
              (verticalTwoStripChildrenEven (m + 1) lam).sum
                (fun mu => tableauDim mu) := by
          apply congrArg₂ (fun x y : Real => x + y)
          · exact Finset.sum_congr rfl (fun mu _ => ih mu)
          · exact Finset.sum_congr rfl (fun mu _ => ih mu)
        _ = tableauDim lam := by
          symm
          exact tableauDim_twoStripChildrenEven_branching_succ m lam

/-- The genuine odd sign-pattern multiset has one label for every standard
tableau, with multiplicity. -/
theorem S05_Lem5_10_oddSignPatternMultiset_card
    (m : Nat) (lam : YoungDiagram (2 * m + 1)) :
    ((S05_oddSignPatternMultiset m lam).card : Real) = tableauDim lam := by
  calc
    ((S05_oddSignPatternMultiset m lam).card : Real) =
        (oneBoxChildrenOdd m lam).sum
          (fun mu => ((S05_evenSignPatternMultiset m mu).card : Real)) := by
      simp [S05_oddSignPatternMultiset]
    _ = (oneBoxChildrenOdd m lam).sum (fun mu => tableauDim mu) := by
      exact Finset.sum_congr rfl
        (fun mu _ => S05_Lem5_10_evenSignPatternMultiset_card m mu)
    _ = tableauDim lam := by
      symm
      exact tableauDim_oneBoxChildrenOdd_branching m lam

@[simp] theorem S05_Lem5_10_liftEvenSignPattern_card
    {m : Nat} (R : Finset (Fin m)) :
    (S05_liftEvenSignPattern R).card = R.card := by
  simp [S05_liftEvenSignPattern]

@[simp] theorem S05_Lem5_10_liftEvenSignPatternWithLast_card
    {m : Nat} (R : Finset (Fin m)) :
    (S05_liftEvenSignPatternWithLast R).card = R.card + 1 := by
  simp [S05_liftEvenSignPatternWithLast, S05_liftEvenSignPattern]

private theorem zeroMultiplicity_add {m : Nat}
    (X Y : Multiset (Finset (Fin m))) :
    S05_zeroSignPatternMultiplicity (X + Y) =
      S05_zeroSignPatternMultiplicity X + S05_zeroSignPatternMultiplicity Y := by
  simp [S05_zeroSignPatternMultiplicity]

private theorem highMultiplicity_add {m : Nat}
    (X Y : Multiset (Finset (Fin m))) :
    S05_highSignPatternMultiplicity (X + Y) =
      S05_highSignPatternMultiplicity X + S05_highSignPatternMultiplicity Y := by
  simp [S05_highSignPatternMultiplicity]

private theorem zeroMultiplicity_finset_sum
    {m : Nat} {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι -> Multiset (Finset (Fin m))) :
    S05_zeroSignPatternMultiplicity (s.sum f) =
      s.sum (fun i => S05_zeroSignPatternMultiplicity (f i)) := by
  induction s using Finset.induction_on with
  | empty => simp [S05_zeroSignPatternMultiplicity]
  | @insert a s ha ih => simp [ha, ih, zeroMultiplicity_add]

private theorem highMultiplicity_finset_sum
    {m : Nat} {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι -> Multiset (Finset (Fin m))) :
    S05_highSignPatternMultiplicity (s.sum f) =
      s.sum (fun i => S05_highSignPatternMultiplicity (f i)) := by
  induction s using Finset.induction_on with
  | empty => simp [S05_highSignPatternMultiplicity]
  | @insert a s ha ih => simp [ha, ih, highMultiplicity_add]

private theorem zeroMultiplicity_map_lift
    {m : Nat} (X : Multiset (Finset (Fin m))) :
    S05_zeroSignPatternMultiplicity
        (X.map S05_liftEvenSignPattern) =
      S05_zeroSignPatternMultiplicity X := by
  rw [S05_zeroSignPatternMultiplicity, Multiset.countP_map,
    S05_zeroSignPatternMultiplicity, Multiset.countP_eq_card_filter]
  simp

private theorem zeroMultiplicity_map_liftWithLast
    {m : Nat} (X : Multiset (Finset (Fin m))) :
    S05_zeroSignPatternMultiplicity
        (X.map S05_liftEvenSignPatternWithLast) = 0 := by
  rw [S05_zeroSignPatternMultiplicity, Multiset.countP_map]
  simp

private theorem highMultiplicity_map_lift
    {m : Nat} (X : Multiset (Finset (Fin m))) :
    S05_highSignPatternMultiplicity
        (X.map S05_liftEvenSignPattern) =
      S05_highSignPatternMultiplicity X := by
  rw [S05_highSignPatternMultiplicity, Multiset.countP_map,
    S05_highSignPatternMultiplicity, Multiset.countP_eq_card_filter]
  simp

private theorem highMultiplicity_map_liftWithLast
    {m : Nat} (X : Multiset (Finset (Fin m))) :
    S05_highSignPatternMultiplicity
        (X.map S05_liftEvenSignPatternWithLast) =
      X.countP (fun R => R.card ≠ 0) := by
  rw [S05_highSignPatternMultiplicity, Multiset.countP_map,
    Multiset.countP_eq_card_filter]
  apply congrArg Multiset.card
  apply Multiset.filter_congr
  intro R _hR
  rw [S05_Lem5_10_liftEvenSignPatternWithLast_card]
  omega

private theorem highMultiplicity_map_liftWithLast_add_zero
    {m : Nat} (X : Multiset (Finset (Fin m))) :
    S05_highSignPatternMultiplicity
          (X.map S05_liftEvenSignPatternWithLast) +
        S05_zeroSignPatternMultiplicity X = X.card := by
  rw [highMultiplicity_map_liftWithLast,
    S05_zeroSignPatternMultiplicity]
  have h := Multiset.card_eq_countP_add_countP
    (p := fun R : Finset (Fin m) => R.card = 0) X
  simpa [Nat.add_comm] using h.symm

private theorem highMultiplicity_map_liftWithLast_cast
    {m : Nat} (X : Multiset (Finset (Fin m))) :
    ((S05_highSignPatternMultiplicity
        (X.map S05_liftEvenSignPatternWithLast) : Nat) : Real) =
      (X.card : Real) - (S05_zeroSignPatternMultiplicity X : Real) := by
  have h := congrArg (fun n : Nat => (n : Real))
    (highMultiplicity_map_liftWithLast_add_zero X)
  push_cast at h
  linarith

/-- Empty labels in the genuine even sign-pattern multiset are counted by
`zEven`. -/
theorem S05_Lem5_10_evenSignPatternMultiset_zeroMultiplicity :
    forall (m : Nat) (lam : YoungDiagram (2 * m)),
      ((S05_zeroSignPatternMultiplicity
          (S05_evenSignPatternMultiset m lam) : Nat) : Real) = zEven m lam := by
  intro m
  induction m with
  | zero =>
      intro lam
      change ((1 : Nat) : Real) = 1
      norm_num
  | succ m ih =>
      intro lam
      calc
        ((S05_zeroSignPatternMultiplicity
            (S05_evenSignPatternMultiset (m + 1) lam) : Nat) : Real) =
            (horizontalTwoStripChildrenEven (m + 1) lam).sum
              (fun mu =>
                ((S05_zeroSignPatternMultiplicity
                    (S05_evenSignPatternMultiset m mu) : Nat) : Real)) := by
          simp [S05_evenSignPatternMultiset, zeroMultiplicity_add,
            zeroMultiplicity_finset_sum, zeroMultiplicity_map_lift,
            zeroMultiplicity_map_liftWithLast]
        _ = (horizontalTwoStripChildrenEven (m + 1) lam).sum
              (fun mu => zEven m mu) := by
          exact Finset.sum_congr rfl (fun mu _ => ih mu)
        _ = zEven (m + 1) lam := by
          rw [zEven]

/-- Weight-at-least-two labels in the genuine even sign-pattern multiset are
counted by `hEvenTableau`. -/
theorem S05_Lem5_10_evenSignPatternMultiset_highMultiplicity :
    forall (m : Nat) (lam : YoungDiagram (2 * m)),
      ((S05_highSignPatternMultiplicity
          (S05_evenSignPatternMultiset m lam) : Nat) : Real) =
        hEvenTableau m lam := by
  intro m
  induction m with
  | zero =>
      intro lam
      simp [S05_evenSignPatternMultiset, S05_highSignPatternMultiplicity,
        hEvenTableau]
  | succ m ih =>
      intro lam
      calc
        ((S05_highSignPatternMultiplicity
            (S05_evenSignPatternMultiset (m + 1) lam) : Nat) : Real) =
            (horizontalTwoStripChildrenEven (m + 1) lam).sum
                (fun mu =>
                  ((S05_highSignPatternMultiplicity
                      (S05_evenSignPatternMultiset m mu) : Nat) : Real)) +
              (verticalTwoStripChildrenEven (m + 1) lam).sum
                (fun mu =>
                  ((S05_highSignPatternMultiplicity
                      ((S05_evenSignPatternMultiset m mu).map
                        S05_liftEvenSignPatternWithLast) : Nat) : Real)) := by
          simp [S05_evenSignPatternMultiset, highMultiplicity_add,
            highMultiplicity_finset_sum, highMultiplicity_map_lift]
        _ =
            (horizontalTwoStripChildrenEven (m + 1) lam).sum
                (fun mu => hEvenTableau m mu) +
              (verticalTwoStripChildrenEven (m + 1) lam).sum
                (fun mu => tableauDim mu - zEven m mu) := by
          apply congrArg₂ (fun x y : Real => x + y)
          · exact Finset.sum_congr rfl (fun mu _ => ih mu)
          · apply Finset.sum_congr rfl
            intro mu _
            rw [highMultiplicity_map_liftWithLast_cast,
              S05_Lem5_10_evenSignPatternMultiset_card,
              S05_Lem5_10_evenSignPatternMultiset_zeroMultiplicity]
            rfl
        _ = hEvenTableau (m + 1) lam := by
          rw [hEvenTableau]

/-- Weight-at-least-two labels in the genuine odd sign-pattern multiset are
counted by `hOddTableau`. -/
theorem S05_Lem5_10_oddSignPatternMultiset_highMultiplicity
    (m : Nat) (lam : YoungDiagram (2 * m + 1)) :
    ((S05_highSignPatternMultiplicity
        (S05_oddSignPatternMultiset m lam) : Nat) : Real) =
      hOddTableau m lam := by
  calc
    ((S05_highSignPatternMultiplicity
        (S05_oddSignPatternMultiset m lam) : Nat) : Real) =
        (oneBoxChildrenOdd m lam).sum
          (fun mu =>
            ((S05_highSignPatternMultiplicity
                (S05_evenSignPatternMultiset m mu) : Nat) : Real)) := by
      simp [S05_oddSignPatternMultiset, highMultiplicity_finset_sum]
    _ = (oneBoxChildrenOdd m lam).sum (fun mu => hEvenTableau m mu) := by
      exact Finset.sum_congr rfl
        (fun mu _ => S05_Lem5_10_evenSignPatternMultiset_highMultiplicity m mu)
    _ = hOddTableau m lam := by
      rw [hOddTableau]

/-- A finite label enumeration counts high labels by the corresponding
multiset multiplicity. -/
theorem S05_Lem5_10_highLabelSum_eq_multiplicity
    {m : Nat} {ι : Type*} [Fintype ι]
    (label : ι -> Finset (Fin m)) :
    (∑ i : ι,
        if S05_matchingCharacterHigh (label i) then (1 : Real) else 0) =
      ((S05_highSignPatternMultiplicity
          (Finset.univ.1.map label) : Nat) : Real) := by
  classical
  calc
    (∑ i : ι,
        if S05_matchingCharacterHigh (label i) then (1 : Real) else 0) =
        ((∑ i : ι,
          if S05_matchingCharacterHigh (label i) then (1 : Nat) else 0 : Nat) :
            Real) := by
      push_cast
      rfl
    _ = ((Finset.univ.filter
          (fun i => S05_matchingCharacterHigh (label i))).card : Real) := by
      congr 1
      simp
    _ = ((S05_highSignPatternMultiplicity
          (Finset.univ.1.map label) : Nat) : Real) := by
      congr 1
      simp [S05_highSignPatternMultiplicity, Multiset.countP_eq_card_filter,
        Multiset.filter_map, S05_matchingCharacterHigh,
        S05_matchingCharacterWeight]
      change
        (Multiset.filter (fun i : ι => 2 <= (label i).card)
          Finset.univ.1).card =
        (Multiset.filter (fun i : ι => 2 <= (label i).card)
          Finset.univ.1).card
      rfl

/-- An enumeration whose label multiset is Definition 5.13 has exactly
`hEvenTableau` high labels. -/
theorem S05_Lem5_10_highLabelCount_of_evenSignPatternMultiset
    {m : Nat} {lam : YoungDiagram (2 * m)}
    {ι : Type*} [Fintype ι]
    (label : ι -> Finset (Fin m))
    (hlabels : Finset.univ.1.map label = S05_evenSignPatternMultiset m lam) :
    (∑ i : ι,
        if S05_matchingCharacterHigh (label i) then (1 : Real) else 0) =
      hEvenTableau m lam := by
  rw [S05_Lem5_10_highLabelSum_eq_multiplicity, hlabels]
  exact S05_Lem5_10_evenSignPatternMultiset_highMultiplicity m lam

/-- An enumeration whose label multiset is Definition 5.14 has exactly
`hOddTableau` high labels. -/
theorem S05_Lem5_10_highLabelCount_of_oddSignPatternMultiset
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    {ι : Type*} [Fintype ι]
    (label : ι -> Finset (Fin m))
    (hlabels : Finset.univ.1.map label = S05_oddSignPatternMultiset m lam) :
    (∑ i : ι,
        if S05_matchingCharacterHigh (label i) then (1 : Real) else 0) =
      hOddTableau m lam := by
  rw [S05_Lem5_10_highLabelSum_eq_multiplicity, hlabels]
  exact S05_Lem5_10_oddSignPatternMultiset_highMultiplicity m lam

/-- Lemma 5.10 scalar-size base case: the empty even diagram has one
zero-weight entry. -/
theorem S05_Lem5_10_evenZeroSignPatternCount_zero
    (lam : YoungDiagram (2 * 0)) :
    S05_evenZeroSignPatternCount 0 lam = 1 := by
  exact S05_evenZeroSignPatternCount_zero lam

/-- Lemma 5.10 scalar-size component: the even zero-weight count has the
horizontal two-strip recursion. -/
theorem S05_Lem5_10_evenZeroSignPatternCount_succ
    (m : Nat) (lam : YoungDiagram (2 * (m + 1))) :
    S05_evenZeroSignPatternCount (m + 1) lam =
      (horizontalTwoStripChildrenEven (m + 1) lam).sum
        (fun mu => S05_evenZeroSignPatternCount m mu) := by
  exact S05_evenZeroSignPatternCount_succ m lam

/-- Lemma 5.10 scalar-size base case: the empty even diagram has no high-weight
entries. -/
theorem S05_Lem5_10_evenHighSignPatternCount_zero
    (lam : YoungDiagram (2 * 0)) :
    S05_evenHighSignPatternCount 0 lam = 0 := by
  exact S05_evenHighSignPatternCount_zero lam

/-- Lemma 5.10 scalar-size component: the even high-weight count has the
horizontal-plus-vertical recursion. -/
theorem S05_Lem5_10_evenHighSignPatternCount_succ
    (m : Nat) (lam : YoungDiagram (2 * (m + 1))) :
    S05_evenHighSignPatternCount (m + 1) lam =
      (horizontalTwoStripChildrenEven (m + 1) lam).sum
          (fun mu => S05_evenHighSignPatternCount m mu) +
        (verticalTwoStripChildrenEven (m + 1) lam).sum
          (fun mu => youngDim mu - S05_evenZeroSignPatternCount m mu) := by
  exact S05_evenHighSignPatternCount_succ m lam

/-- Lemma 5.10 scalar-size component: the odd high-weight count is the sum of
even high-weight counts over one-box removals. -/
theorem S05_Lem5_10_oddHighSignPatternCount_eq_evenHigh_sum
    (m : Nat) (lam : YoungDiagram (2 * m + 1)) :
    S05_oddHighSignPatternCount m lam =
      (oneBoxChildrenOdd m lam).sum
        (fun mu => S05_evenHighSignPatternCount m mu) := by
  exact S05_oddHighSignPatternCount_eq_evenHigh_sum m lam

/-- Lemma 5.10 dimension-size component: the even two-strip dimension size
recursion, supplied by the named branching input. -/
theorem S05_Lem5_10_youngDim_twoStrip_size
    [TwoStripDimensionBranchingAssumption] (m : Nat) (hm : 2 <= m)
    (lam : YoungDiagram (2 * m)) :
    youngDim lam =
      (horizontalTwoStripChildrenEven m lam).sum (fun mu => youngDim mu) +
        (verticalTwoStripChildrenEven m lam).sum (fun mu => youngDim mu) := by
  exact youngDim_twoStrip_branching_input m hm lam

/-- Lemma 5.10 dimension-size component: the odd one-box dimension size
recursion, supplied by the named branching input except in the proved small
cases. -/
theorem S05_Lem5_10_youngDim_oneBox_size
    [OneBoxDimensionBranchingPositiveAssumption] (m : Nat)
    (lam : YoungDiagram (2 * m + 1)) :
    youngDim lam = (oneBoxChildrenOdd m lam).sum (fun mu => youngDim mu) := by
  exact youngDim_oneBox_branching_input m lam

/-- Lemma 5.10 tableau-count component: the assumption-free two-strip size
recursion for standard-tableau counts. -/
theorem S05_Lem5_10_tableauDim_twoStrip_size
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1)) :
    tableauDim lam =
      (horizontalTwoStripChildrenSized lam).sum (fun mu => tableauDim mu) +
        (verticalTwoStripChildrenSized lam).sum (fun mu => tableauDim mu) := by
  exact S05_Lem5_08_tableauDim_twoStrip_branching_sized lam

/-- Lemma 5.10 tableau-count component: the assumption-free even two-strip size
recursion in the indexed Section 5 notation. -/
theorem S05_Lem5_10_tableauDim_twoStripChildrenEven_size_succ
    (m : Nat) (lam : YoungDiagram (2 * (m + 1))) :
    tableauDim lam =
      (horizontalTwoStripChildrenEven (m + 1) lam).sum
          (fun mu => tableauDim mu) +
        (verticalTwoStripChildrenEven (m + 1) lam).sum
          (fun mu => tableauDim mu) := by
  exact S05_Lem5_08_tableauDim_twoStripChildrenEven_branching_succ m lam

/-- Lemma 5.10 tableau-count component: the assumption-free one-box size
recursion for standard-tableau counts. -/
theorem S05_Lem5_10_tableauDim_oneBox_size
    {n : Nat} (lam : YoungDiagram (n + 1)) :
    tableauDim lam =
      (oneBoxChildrenSized lam).sum (fun mu => tableauDim mu) := by
  exact S05_Lem5_09_tableauDim_oneBox_branching lam

/-- Lemma 5.10 tableau-count component: the assumption-free odd one-box size
recursion in the indexed Section 5 notation. -/
theorem S05_Lem5_10_tableauDim_oneBoxChildrenOdd_size
    (m : Nat) (lam : YoungDiagram (2 * m + 1)) :
    tableauDim lam =
      (oneBoxChildrenOdd m lam).sum (fun mu => tableauDim mu) := by
  exact S05_Lem5_09_tableauDim_oneBoxChildrenOdd_branching m lam

end DictatorshipTesting
