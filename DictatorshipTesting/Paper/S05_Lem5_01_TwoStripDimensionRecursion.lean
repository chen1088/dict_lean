import DictatorshipTesting.Paper.Defs

/-!
Paper statement: Lemma 5.1 (`lem:dimension-two-strip-recurrence`)
Title in paper: Dimension recursion.

Status: external representation-theoretic input in the current Lean
development, from two-strip Pieri/Littlewood--Richardson branching.  It should
be proved internally only after a formal Specht-module/branching library is
available.
-/

/-!
# Young-dimension branching input

This file isolates the dimension shadow of the two-strip
Pieri/Littlewood-Richardson branching rule used in Section 5.

The finite Z-bound induction only needs this scalar consequence:

`d_lambda = sum_{horizontal children} d_mu + sum_{vertical children} d_mu`.

It is intentionally kept out of `S05_Lem5_10_ZBoundCertificate`: it is a standard
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

end DictatorshipTesting
