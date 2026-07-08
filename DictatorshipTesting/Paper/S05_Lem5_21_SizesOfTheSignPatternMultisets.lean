import DictatorshipTesting.Paper.S05_Def5_18_OddSignPatternMultiset
import DictatorshipTesting.Paper.S05_Lem5_19_TwoBoxDimensionRecursion
import DictatorshipTesting.Paper.S05_Lem5_20_OneBoxDimensionRecursion

/-
Direct reverse imports:
- `DictatorshipTesting`
-/


/-!
Paper statement: Lemma 5.21 (`lem:X-size`)
Title in paper: Sizes of the sign-pattern multisets.

Status: proven. Paper-facing owner file for the rewritten Section 5 statement.  The
current finite scaffold uses the scalar counts `zEven`, `hEven`, and `hOdd`.
The `youngDim` size wrappers assume the named dimension branching inputs,
while the `tableauDim` size wrappers are assumption-free.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.21 scalar-size base case: the empty even diagram has one
zero-weight entry. -/
theorem S05_Lem5_21_evenZeroSignPatternCount_zero
    (lam : YoungDiagram (2 * 0)) :
    S05_evenZeroSignPatternCount 0 lam = 1 := by
  exact S05_evenZeroSignPatternCount_zero lam

/-- Lemma 5.21 scalar-size component: the even zero-weight count has the
horizontal two-strip recursion. -/
theorem S05_Lem5_21_evenZeroSignPatternCount_succ
    (m : Nat) (lam : YoungDiagram (2 * (m + 1))) :
    S05_evenZeroSignPatternCount (m + 1) lam =
      (horizontalTwoStripChildrenEven (m + 1) lam).sum
        (fun mu => S05_evenZeroSignPatternCount m mu) := by
  exact S05_evenZeroSignPatternCount_succ m lam

/-- Lemma 5.21 scalar-size base case: the empty even diagram has no high-weight
entries. -/
theorem S05_Lem5_21_evenHighSignPatternCount_zero
    (lam : YoungDiagram (2 * 0)) :
    S05_evenHighSignPatternCount 0 lam = 0 := by
  exact S05_evenHighSignPatternCount_zero lam

/-- Lemma 5.21 scalar-size component: the even high-weight count has the
horizontal-plus-vertical recursion. -/
theorem S05_Lem5_21_evenHighSignPatternCount_succ
    (m : Nat) (lam : YoungDiagram (2 * (m + 1))) :
    S05_evenHighSignPatternCount (m + 1) lam =
      (horizontalTwoStripChildrenEven (m + 1) lam).sum
          (fun mu => S05_evenHighSignPatternCount m mu) +
        (verticalTwoStripChildrenEven (m + 1) lam).sum
          (fun mu => youngDim mu - S05_evenZeroSignPatternCount m mu) := by
  exact S05_evenHighSignPatternCount_succ m lam

/-- Lemma 5.21 scalar-size component: the odd high-weight count is the sum of
even high-weight counts over one-box removals. -/
theorem S05_Lem5_21_oddHighSignPatternCount_eq_evenHigh_sum
    (m : Nat) (lam : YoungDiagram (2 * m + 1)) :
    S05_oddHighSignPatternCount m lam =
      (oneBoxChildrenOdd m lam).sum
        (fun mu => S05_evenHighSignPatternCount m mu) := by
  exact S05_oddHighSignPatternCount_eq_evenHigh_sum m lam

/-- Lemma 5.21 dimension-size component: the even two-strip dimension size
recursion, supplied by the named branching input. -/
theorem S05_Lem5_21_youngDim_twoStrip_size
    [TwoStripDimensionBranchingAssumption] (m : Nat) (hm : 2 <= m)
    (lam : YoungDiagram (2 * m)) :
    youngDim lam =
      (horizontalTwoStripChildrenEven m lam).sum (fun mu => youngDim mu) +
        (verticalTwoStripChildrenEven m lam).sum (fun mu => youngDim mu) := by
  exact youngDim_twoStrip_branching_input m hm lam

/-- Lemma 5.21 dimension-size component: the odd one-box dimension size
recursion, supplied by the named branching input except in the proved small
cases. -/
theorem S05_Lem5_21_youngDim_oneBox_size
    [OneBoxDimensionBranchingPositiveAssumption] (m : Nat)
    (lam : YoungDiagram (2 * m + 1)) :
    youngDim lam = (oneBoxChildrenOdd m lam).sum (fun mu => youngDim mu) := by
  exact youngDim_oneBox_branching_input m lam

/-- Lemma 5.21 tableau-count component: the assumption-free two-strip size
recursion for standard-tableau counts. -/
theorem S05_Lem5_21_tableauDim_twoStrip_size
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1)) :
    tableauDim lam =
      (horizontalTwoStripChildrenSized lam).sum (fun mu => tableauDim mu) +
        (verticalTwoStripChildrenSized lam).sum (fun mu => tableauDim mu) := by
  exact S05_Lem5_19_tableauDim_twoStrip_branching_sized lam

/-- Lemma 5.21 tableau-count component: the assumption-free even two-strip size
recursion in the indexed Section 5 notation. -/
theorem S05_Lem5_21_tableauDim_twoStripChildrenEven_size_succ
    (m : Nat) (lam : YoungDiagram (2 * (m + 1))) :
    tableauDim lam =
      (horizontalTwoStripChildrenEven (m + 1) lam).sum
          (fun mu => tableauDim mu) +
        (verticalTwoStripChildrenEven (m + 1) lam).sum
          (fun mu => tableauDim mu) := by
  exact S05_Lem5_19_tableauDim_twoStripChildrenEven_branching_succ m lam

/-- Lemma 5.21 tableau-count component: the assumption-free one-box size
recursion for standard-tableau counts. -/
theorem S05_Lem5_21_tableauDim_oneBox_size
    {n : Nat} (lam : YoungDiagram (n + 1)) :
    tableauDim lam =
      (oneBoxChildrenSized lam).sum (fun mu => tableauDim mu) := by
  exact S05_Lem5_20_tableauDim_oneBox_branching lam

/-- Lemma 5.21 tableau-count component: the assumption-free odd one-box size
recursion in the indexed Section 5 notation. -/
theorem S05_Lem5_21_tableauDim_oneBoxChildrenOdd_size
    (m : Nat) (lam : YoungDiagram (2 * m + 1)) :
    tableauDim lam =
      (oneBoxChildrenOdd m lam).sum (fun mu => tableauDim mu) := by
  exact S05_Lem5_20_tableauDim_oneBoxChildrenOdd_branching m lam

end DictatorshipTesting
