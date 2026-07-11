import DictatorshipTesting.Paper.Defs.S03_IntDef_NearPerfectMatchingToOrdered
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S03_IntDef_OneTrialDeltaSqExpectation`
-/


/-!
Definition file for `matchingMeanProjectionError`.
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
