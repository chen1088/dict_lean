import DictatorshipTesting.Paper.Defs.S05_IntDef_OneBoxChildrenOdd
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S05_Def5_24_TableauEvenHeight`
- `DictatorshipTesting.Paper.Defs.S05_IntDef_HEven`
- `DictatorshipTesting.Paper.S05_Lem5_22_WeightZeroEntriesAreNeverAMajority`
-/


/-!
Definition file for `zEven`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Number of weight-zero entries in the even matching-branching multiset. -/
def zEven : (m : ℕ) → YoungDiagram (2 * m) → ℝ
  | 0, _ => 1
  | m + 1, lam =>
      (horizontalTwoStripChildrenEven (m + 1) lam).sum
        (fun mu => zEven m mu)

end DictatorshipTesting
