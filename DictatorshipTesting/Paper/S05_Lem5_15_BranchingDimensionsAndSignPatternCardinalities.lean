import DictatorshipTesting.Paper.S05_Int_OneBoxDimensionRecursion
import DictatorshipTesting.Paper.S05_Int_SignPatternCardinalities
import DictatorshipTesting.Paper.S05_Int_TwoBoxDimensionRecursion

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_16_MatchingSubgroupEigenbasis`
- `DictatorshipTesting.Paper.S05_Lem5_24_WeightZeroEntriesAreNeverAMajority`
- `DictatorshipTesting.Paper.S05_Lem5_25_EvenCertificate`
- `DictatorshipTesting.Paper.S05_Lem5_26_OddCertificate`
-/

/-!
# Lemma 5.15: Branching dimensions and sign-pattern cardinalities

This is `lem:dimension-two-strip-recurrence`, together with its one-box and
sign-pattern-cardinality aliases, in the STOC 2027 paper.
-/

namespace DictatorshipTesting

/-- Lemma 5.15: the two-box dimension recursion. -/
theorem S05_Lem5_15_tableauDim_twoStrip_branching_sized
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1)) :
    tableauDim lam =
      (horizontalTwoStripChildrenSized lam).sum (fun mu => tableauDim mu) +
        (verticalTwoStripChildrenSized lam).sum (fun mu => tableauDim mu) :=
  S05_twoBoxDimension_tableauDim_twoStrip_branching_sized lam

/-- Lemma 5.15: the one-box dimension recursion. -/
theorem S05_Lem5_15_tableauDim_oneBox_branching
    {n : Nat} (lam : YoungDiagram (n + 1)) :
    tableauDim lam =
      (oneBoxChildrenSized lam).sum (fun mu => tableauDim mu) :=
  S05_oneBoxDimension_tableauDim_oneBox_branching lam

/-- Lemma 5.15: the even sign-pattern multiset has one entry per tableau. -/
theorem S05_Lem5_15_evenSignPatternMultiset_card :
    ∀ (m : Nat) (lam : YoungDiagram (2 * m)),
      ((S05_evenSignPatternMultiset m lam).card : Real) = tableauDim lam :=
  S05_signPatternCardinality_evenSignPatternMultiset_card

/-- Lemma 5.15: the odd sign-pattern multiset has one entry per tableau. -/
theorem S05_Lem5_15_oddSignPatternMultiset_card
    (m : Nat) (lam : YoungDiagram (2 * m + 1)) :
    ((S05_oddSignPatternMultiset m lam).card : Real) = tableauDim lam :=
  S05_signPatternCardinality_oddSignPatternMultiset_card m lam

end DictatorshipTesting
