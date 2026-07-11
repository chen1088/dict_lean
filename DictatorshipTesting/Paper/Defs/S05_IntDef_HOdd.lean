import DictatorshipTesting.Paper.Defs.S05_IntDef_HEven
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S05_Def5_10b_OddSignPatternMultiset`
- `DictatorshipTesting.Paper.Defs.S05_IntDef_MatchingRestrictionOddInput`
- `DictatorshipTesting.Paper.Defs.S05_IntDef_MatchingSpectralGapConstant`
- `DictatorshipTesting.Paper.S05_Lem5_35_OddCertificate`
-/


/-!
Definition file for `hOdd`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Number of weight-at-least-two entries in the odd matching-branching multiset. -/
def hOdd (m : ℕ) (lam : YoungDiagram (2 * m + 1)) : ℝ :=
  (oneBoxChildrenOdd m lam).sum (fun mu => hEven m mu)

end DictatorshipTesting
