import DictatorshipTesting.Paper.Defs

/-!
# Young-dimension one-box branching input

This file isolates the dimension shadow of the ordinary one-box branching rule
used in the odd Section 5 certificate.

For a Young diagram `lambda` with `2*m+1` boxes, the Specht dimension is the
sum of the dimensions of its one-box children.  This is the standard
Pieri/Littlewood-Richardson branching input for restricting from `S_{2m+1}` to
`S_{2m}`.
-/

noncomputable section

namespace DictatorshipTesting

/-- Dimension shadow of the ordinary one-box branching rule. -/
theorem youngDim_oneBox_branching_input (m : ℕ)
    (lam : YoungDiagram (2 * m + 1)) :
    youngDim lam = (oneBoxChildrenOdd m lam).sum (fun mu => youngDim mu) := by
  sorry

end DictatorshipTesting
