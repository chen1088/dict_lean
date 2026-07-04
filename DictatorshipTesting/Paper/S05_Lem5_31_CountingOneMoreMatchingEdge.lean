import DictatorshipTesting.Paper.Defs

/-!
# Lemma 5.31: Counting one more matching edge

This is the recurrence lemma containing equations `eq:z-recurrence` and
`eq:h-recurrence`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Lemma 5.31: counting one more matching edge.  The theorem name is kept from
the older scaffold for compatibility. -/
theorem L5_3_CountingOneMoreMatchingEdge (m : ℕ) (hm : 1 ≤ m)
    (lam : YoungDiagram (2 * m)) :
    zEven m lam =
        (horizontalTwoStripChildrenEven m lam).sum
          (fun mu => zEven (m - 1) mu) ∧
      hEven m lam =
        (horizontalTwoStripChildrenEven m lam).sum
            (fun mu => hEven (m - 1) mu) +
          (verticalTwoStripChildrenEven m lam).sum
            (fun mu => youngDim mu - zEven (m - 1) mu) := by
  cases m with
  | zero =>
      omega
  | succ m =>
      simp [zEven, hEven]

/-- Lemma 5.31 paper-numbered alias: counting one more matching edge. -/
theorem S05_Lem5_31_counting_one_more_matching_edge (m : ℕ) (hm : 1 ≤ m)
    (lam : YoungDiagram (2 * m)) :
    zEven m lam =
        (horizontalTwoStripChildrenEven m lam).sum
          (fun mu => zEven (m - 1) mu) ∧
      hEven m lam =
        (horizontalTwoStripChildrenEven m lam).sum
            (fun mu => hEven (m - 1) mu) +
          (verticalTwoStripChildrenEven m lam).sum
            (fun mu => youngDim mu - zEven (m - 1) mu) := by
  exact L5_3_CountingOneMoreMatchingEdge m hm lam

end DictatorshipTesting
