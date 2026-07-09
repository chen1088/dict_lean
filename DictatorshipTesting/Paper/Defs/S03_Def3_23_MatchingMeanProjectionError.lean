import DictatorshipTesting.Paper.Defs.S03_Def3_22_NearPerfectMatchingToOrdered
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S03_Def3_24_OneTrialDeltaSqExpectation`
-/


/-!
Definition file for `matchingMeanProjectionError`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Mean, over a uniformly random near-perfect matching, of `||(I-P_M)F||_2^2`. -/
def matchingMeanProjectionError {n : ℕ}
    (F : Perm (Fin n) → ℝ) : ℝ :=
  (∑ M : NearPerfectMatching n,
    matchingLocalProjectionError F M.toOrdered) /
      (Fintype.card (NearPerfectMatching n) : ℝ)

end DictatorshipTesting
