import DictatorshipTesting.Paper.Defs.S05_IntDef_ZEven
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S05_Def5_13_EvenSignPatternMultiset`
- `DictatorshipTesting.Paper.Defs.S05_Def5_18_MatchingRestrictionEvenInput`
- `DictatorshipTesting.Paper.Defs.S05_IntDef_HOdd`
- `DictatorshipTesting.Paper.S05_Lem5_21_CountingOneMoreMatchingEdge`
- `DictatorshipTesting.Paper.S05_Lem5_24_EvenCertificate`
-/


/-!
Definition file for `hEven`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Number of weight-at-least-two entries in the even matching-branching multiset. -/
def hEven : (m : ℕ) → YoungDiagram (2 * m) → ℝ
  | 0, _ => 0
  | m + 1, lam =>
      (horizontalTwoStripChildrenEven (m + 1) lam).sum
          (fun mu => hEven m mu) +
        (verticalTwoStripChildrenEven (m + 1) lam).sum
          (fun mu => youngDim mu - zEven m mu)

end DictatorshipTesting
