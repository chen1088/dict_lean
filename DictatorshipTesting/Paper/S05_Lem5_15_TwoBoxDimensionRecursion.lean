import DictatorshipTesting.Paper.Aux_TableauDimension

/-!
Paper statement: Lemma 5.15 (`lem:dimension-two-strip-recurrence`)
Title in paper: Two-box dimension recursion.

Status: the `youngDim` statement remains an external representation-theoretic
input, because `youngDim` is currently the hook-length dimension proxy.  The
final section exposes the assumption-free tableau-count layer: fixed ordered
two-step deletion fibers, the ordered two-step deletion recursion, the
multiplicity-preserving reindexing by tagged horizontal/vertical two-strip
children, and the sized two-strip branching theorem for `tableauDim`.
-/

/-!
# Young-dimension branching input for Lemma 5.15

This file isolates the dimension shadow of the two-strip
Pieri/Littlewood-Richardson branching rule used in Section 5.

The finite Z-bound induction only needs this scalar consequence:

`d_lambda = sum_{horizontal children} d_mu + sum_{vertical children} d_mu`.

It is intentionally kept out of `S05_Lem5_32_WeightZeroEntriesAreNeverAMajority`: it is a standard
representation-theoretic branching input, not an internal finite certificate
gap.
-/

noncomputable section

namespace DictatorshipTesting

/-- Explicit assumption class for the dimension shadow of the two-strip
branching rule.  Keeping this as a typeclass makes downstream certificate
theorems visibly conditional without introducing a global postulate or hidden
proof hole. -/
class TwoStripDimensionBranchingAssumption : Prop where
  branch : ∀ (m : ℕ), 2 ≤ m → ∀ lam : YoungDiagram (2 * m),
    youngDim lam =
      (horizontalTwoStripChildrenEven m lam).sum (fun mu => youngDim mu) +
        (verticalTwoStripChildrenEven m lam).sum (fun mu => youngDim mu)

/-- External Specht/Pieri dimension-branching input.

Reference: James--Kerber, *The Representation Theory of the Symmetric Group*,
Section 2.8.13 (Littlewood--Richardson rule), as quoted for restriction to
Young subgroups in Bowman--De Visscher--Orellana, arXiv:1210.5579, Theorem 1.1
and the paragraph following it. Specializing the second factor to the two
partitions of `2`, `(2)` and `(1,1)`, gives the horizontal/vertical two-strip
Pieri cases. Taking dimensions gives this recursion. -/
axiom twoStripDimensionBranchingAssumption_from_specht_pieri :
  TwoStripDimensionBranchingAssumption

attribute [instance] twoStripDimensionBranchingAssumption_from_specht_pieri

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

theorem S05_Lem5_15_tableauDim_fixed_twoStepDeletion
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam) :
    ((Fintype.card (TwoStepDeletionTableaux lam p) : Nat) : ℝ) =
      tableauDim (deleteTwoRemovableRowsDiagram lam p) := by
  exact tableauDim_fixed_twoStepDeletion lam p

theorem S05_Lem5_15_tableauDim_ordered_twoStep_branching
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1)) :
    tableauDim lam =
      ∑ p : TwoStepRemovableRows lam,
        tableauDim (deleteTwoRemovableRowsDiagram lam p) := by
  exact tableauDim_eq_sum_twoStepRemovableRows lam

theorem S05_Lem5_15_twoStepDeletion_horizontal_or_vertical
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam) :
    IsHorizontalTwoStripChild lam (deleteTwoRemovableRowsDiagram lam p) ∨
      IsVerticalTwoStripChild lam (deleteTwoRemovableRowsDiagram lam p) := by
  exact deleteTwoRemovableRows_horizontal_or_vertical lam p

/-- The multiplicity-preserving reindexing between ordered two-step deletions
and tagged horizontal/vertical two-strip children.  Disconnected two-box skew
shapes appear once under each tag, matching the two deletion orders. -/
noncomputable def S05_Lem5_15_twoStepRemovableRowsEquivTaggedTwoStripChildren
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1)) :
    TwoStepRemovableRows lam ≃ TaggedTwoStripChildrenSized lam :=
  twoStepRemovableRowsEquivTaggedTwoStripChildren lam

theorem S05_Lem5_15_sum_twoStepRemovableRows_eq_sum_taggedTwoStripChildren
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1)) :
    (∑ p : TwoStepRemovableRows lam,
        tableauDim (deleteTwoRemovableRowsDiagram lam p))
      =
    ∑ x : TaggedTwoStripChildrenSized lam,
      tableauDim (taggedTwoStripChildDiagram x) := by
  exact sum_twoStepRemovableRows_eq_sum_taggedTwoStripChildren lam

theorem S05_Lem5_15_tableauDim_twoStrip_branching_sized
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1)) :
    tableauDim lam =
      (horizontalTwoStripChildrenSized lam).sum (fun mu => tableauDim mu) +
        (verticalTwoStripChildrenSized lam).sum (fun mu => tableauDim mu) := by
  exact tableauDim_twoStrip_branching_sized lam

theorem S05_Lem5_15_tableauDim_twoStripChildrenEven_branching_succ
    (m : Nat) (lam : YoungDiagram (2 * (m + 1))) :
    tableauDim lam =
      (horizontalTwoStripChildrenEven (m + 1) lam).sum (fun mu => tableauDim mu) +
        (verticalTwoStripChildrenEven (m + 1) lam).sum
          (fun mu => tableauDim mu) := by
  exact tableauDim_twoStripChildrenEven_branching_succ m lam

end DictatorshipTesting
