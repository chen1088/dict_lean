import DictatorshipTesting.Paper.Aux_TableauDimension

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_21_SizesOfTheSignPatternMultisets`
- `DictatorshipTesting.Paper.S05_Lem5_36_WeightZeroEntriesAreNeverAMajority`
-/


/-!
Paper statement: Lemma 5.19 (`lem:dimension-two-strip-recurrence`)
Title in paper: Two-box dimension recursion.

Status: proven. The paper-facing Section 5 route uses the assumption-free
`tableauDim` two-strip recursion proved below.  The older `youngDim` wrapper is
kept only as an explicit external-alternative theorem requiring
`[TwoStripDimensionBranchingAssumption]`; this file no longer provides a
bundled instance for that assumption.
-/

/-!
# Young-dimension branching interface for the older route

This file isolates the dimension shadow of the two-strip
Pieri/Littlewood-Richardson branching rule used by the older `youngDim` route.
The current Section 5 proof spine uses the proved `tableauDim` recursion below.

The finite Z-bound induction only needs this scalar consequence:

`d_lambda = sum_{horizontal children} d_mu + sum_{vertical children} d_mu`.

No instance is registered here; callers of the older route must carry
`[TwoStripDimensionBranchingAssumption]` explicitly.
-/

noncomputable section

namespace DictatorshipTesting

/-- Explicit assumption class for the dimension shadow of the two-strip
branching rule.  Keeping this as a typeclass makes downstream certificate
theorems state their required external input without introducing a hidden proof
hole. -/
class TwoStripDimensionBranchingAssumption : Prop where
  branch : ∀ (m : ℕ), 2 ≤ m → ∀ lam : YoungDiagram (2 * m),
    youngDim lam =
      (horizontalTwoStripChildrenEven m lam).sum (fun mu => youngDim mu) +
        (verticalTwoStripChildrenEven m lam).sum (fun mu => youngDim mu)

/-- Dimension shadow of the two-strip branching rule, available from the
explicit assumption class. -/
theorem youngDim_twoStrip_branching_input
    [TwoStripDimensionBranchingAssumption] (m : ℕ) (hm : 2 ≤ m)
    (lam : YoungDiagram (2 * m)) :
    youngDim lam =
      (horizontalTwoStripChildrenEven m lam).sum (fun mu => youngDim mu) +
        (verticalTwoStripChildrenEven m lam).sum (fun mu => youngDim mu) := by
  exact TwoStripDimensionBranchingAssumption.branch m hm lam

/-!
## Tableau-count replacement layer

These wrappers are assumption-free and use `tableauDim`, the count of standard Young
tableaux.  They prove the ordered two-step deletion recursion and reindex that
ordered sum by the tagged horizontal/vertical two-strip child sets.
-/

theorem S05_Lem5_19_tableauDim_fixed_twoStepDeletion
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam) :
    ((Fintype.card (TwoStepDeletionTableaux lam p) : Nat) : ℝ) =
      tableauDim (deleteTwoRemovableRowsDiagram lam p) := by
  exact tableauDim_fixed_twoStepDeletion lam p

theorem S05_Lem5_19_tableauDim_ordered_twoStep_branching
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1)) :
    tableauDim lam =
      ∑ p : TwoStepRemovableRows lam,
        tableauDim (deleteTwoRemovableRowsDiagram lam p) := by
  exact tableauDim_eq_sum_twoStepRemovableRows lam

theorem S05_Lem5_19_twoStepDeletion_horizontal_or_vertical
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam) :
    IsHorizontalTwoStripChild lam (deleteTwoRemovableRowsDiagram lam p) ∨
      IsVerticalTwoStripChild lam (deleteTwoRemovableRowsDiagram lam p) := by
  exact deleteTwoRemovableRows_horizontal_or_vertical lam p

/-- The multiplicity-preserving reindexing between ordered two-step deletions
and tagged horizontal/vertical two-strip children.  Disconnected two-box skew
shapes appear once under each tag, matching the two deletion orders. -/
noncomputable def S05_Lem5_19_twoStepRemovableRowsEquivTaggedTwoStripChildren
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1)) :
    TwoStepRemovableRows lam ≃ TaggedTwoStripChildrenSized lam :=
  twoStepRemovableRowsEquivTaggedTwoStripChildren lam

theorem S05_Lem5_19_sum_twoStepRemovableRows_eq_sum_taggedTwoStripChildren
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1)) :
    (∑ p : TwoStepRemovableRows lam,
        tableauDim (deleteTwoRemovableRowsDiagram lam p))
      =
    ∑ x : TaggedTwoStripChildrenSized lam,
      tableauDim (taggedTwoStripChildDiagram x) := by
  exact sum_twoStepRemovableRows_eq_sum_taggedTwoStripChildren lam

theorem S05_Lem5_19_tableauDim_twoStrip_branching_sized
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1)) :
    tableauDim lam =
      (horizontalTwoStripChildrenSized lam).sum (fun mu => tableauDim mu) +
        (verticalTwoStripChildrenSized lam).sum (fun mu => tableauDim mu) := by
  exact tableauDim_twoStrip_branching_sized lam

theorem S05_Lem5_19_tableauDim_twoStripChildrenEven_branching_succ
    (m : Nat) (lam : YoungDiagram (2 * (m + 1))) :
    tableauDim lam =
      (horizontalTwoStripChildrenEven (m + 1) lam).sum (fun mu => tableauDim mu) +
        (verticalTwoStripChildrenEven (m + 1) lam).sum
          (fun mu => tableauDim mu) := by
  exact tableauDim_twoStripChildrenEven_branching_succ m lam

end DictatorshipTesting
