import DictatorshipTesting.Paper.Defs

/-!
Paper statement: Lemma 5.1 (`lem:dimension-two-strip-recurrence`)
Title in paper: Dimension recursion.

Status: standard representation-theoretic input from two-strip
Pieri/Littlewood--Richardson branching.
-/

/-!
# Young-dimension branching input

This file isolates the dimension shadow of the two-strip
Pieri/Littlewood-Richardson branching rule used in Section 5.

The finite Z-bound induction only needs this scalar consequence:

`d_lambda = sum_{horizontal children} d_mu + sum_{vertical children} d_mu`.

It is intentionally kept out of `S05_Lem5_10_ZBoundCertificate`: it is a standard
branching-theory input, not an internal finite induction step.
-/

noncomputable section

namespace DictatorshipTesting

/-- Dimension shadow of the two-strip branching rule. -/
theorem youngDim_twoStrip_branching_input (m : ℕ) (hm : 2 ≤ m)
    (lam : YoungDiagram (2 * m)) :
    youngDim lam =
      (horizontalTwoStripChildrenEven m lam).sum (fun mu => youngDim mu) +
        (verticalTwoStripChildrenEven m lam).sum (fun mu => youngDim mu) := by
  sorry

end DictatorshipTesting
