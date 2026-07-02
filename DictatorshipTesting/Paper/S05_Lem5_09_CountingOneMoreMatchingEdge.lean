import DictatorshipTesting.Paper.Defs

/-!
# Lemma 5.9: Counting one more matching edge

This is the recurrence lemma containing equations `eq:z-recurrence` and
`eq:h-recurrence`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Lemma 5.9: counting one more matching edge.  The theorem name is kept from
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

end DictatorshipTesting
