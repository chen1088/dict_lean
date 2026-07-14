import DictatorshipTesting.Paper.Defs.S05_IntDef_HEven
import DictatorshipTesting.Paper.Defs.S05_Def5_10a_EvenSignPatternMultiset

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_18_WeightZeroEntriesAreNeverAMajority`
- `DictatorshipTesting.Paper.S05_Lem5_19_EvenCertificate`
-/
/-!
Paper statement: Lemma 5.17 (`lem:counting-one-more-matching-edge`)
Title in paper: Counting one more matching edge: the `z_m` and `h_m`
recurrences.

This is the recurrence lemma containing equations `eq:z-recurrence` and
`eq:h-recurrence`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Lemma 5.17: counting one more matching edge. -/
theorem S05_Lem5_17_CountingOneMoreMatchingEdge (m : ℕ) (hm : 1 ≤ m)
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
