import DictatorshipTesting.Paper.Defs.S04_Def4_01b_MatchingLocalHighDegreeEnergy
/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.Defs.S04_Def4_02b_MatchingLocalProjectionError`
- `DictatorshipTesting.Paper.S04_Int_MatchingLocalProjection`
-/


/-!
Definition file for `matchingLocalProjection`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- The matching-local projection `P_M`, implemented by taking the degree-at-most-one
Fourier truncation on the matching cube based at the queried permutation and
evaluating it at the cube origin.  Lemma 4.4 proves this agrees with the
representative-independent coset formula. -/
def matchingLocalProjection {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) (F : Perm α → ℝ) : Perm α → ℝ :=
  fun π =>
    cubeLowDegreeOnePart (fun x : Cube M.edgeCount => F (π * M.tau x))
      (cubeZero M.edgeCount)

end DictatorshipTesting
