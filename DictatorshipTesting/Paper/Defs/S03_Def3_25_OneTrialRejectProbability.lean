import DictatorshipTesting.Paper.Defs.S03_Def3_24_OneTrialDeltaSqExpectation
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S03_Def3_26_MatchingLowConvolution`
- `DictatorshipTesting.Paper.S01_Thm1_01_MainIntro`
-/


/-!
Definition file for `oneTrialRejectProbability`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Rejection probability of one matching-cube trial on a Boolean oracle. -/
def oneTrialRejectProbability {n : ℕ}
    (f : BoolFn (Fin n)) : ℝ :=
  (∑ M : NearPerfectMatching n,
    (∑ π : Perm (Fin n),
      (∑ c : CubeDirectionColor (n / 2),
        if matchingTrialDelta f M.toOrdered π c = 0 then (0 : ℝ) else 1) /
          (Fintype.card (CubeDirectionColor (n / 2)) : ℝ)) /
        (Fintype.card (Perm (Fin n)) : ℝ)) /
      (Fintype.card (NearPerfectMatching n) : ℝ)

end DictatorshipTesting
