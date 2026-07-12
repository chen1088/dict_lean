import DictatorshipTesting.Paper.Defs.S04_Def4_01b_MatchingLocalHighDegreeEnergy
import DictatorshipTesting.Paper.S02_Lem2_03_CubeParseval
import DictatorshipTesting.Paper.Defs.S04_Def4_01a_IsMatchingLocalDegreeOne
/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.Defs.S04_Def4_02b_MatchingLocalProjectionError`
- `DictatorshipTesting.Paper.Defs.S05_Def5_12a_MatchingIdempotents`
- `DictatorshipTesting.Paper.S04_Cor4_05_U1Local`
- `DictatorshipTesting.Paper.S04_Int_MatchingLocalProjection`
- `DictatorshipTesting.Paper.S04_Lem4_02_PMIndependentOfRepresentatives`
- `DictatorshipTesting.Paper.S04_Prop4_03_MatchingLocalTruncationOrthogonalProjection`
- `DictatorshipTesting.Paper.S04_Prop4_08_SquareEnergyControlsGlobalDegree`
- `DictatorshipTesting.Paper.S05_Lem5_17_LocalTruncationOnAMatchingCharacter`
- `DictatorshipTesting.Paper.S05_Lem5_19_LocalTruncationAsConvolution`
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
