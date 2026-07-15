import DictatorshipTesting.Paper.Defs.S03_IntDef_PermInner
import DictatorshipTesting.Paper.S02_Lem2_03_CubeParseval
import DictatorshipTesting.Paper.Defs.S02_IntDef_L2DistSq

open AlgebraicLibrary

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.Defs.S03_IntDef_NearPerfectMatching`
- `DictatorshipTesting.Paper.Defs.S05_Def5_12a_MatchingIdempotents`
- `DictatorshipTesting.Paper.S04_Lem4_03_GlobalDegreeOneIsLocallyDegreeOne`
- `DictatorshipTesting.Paper.S04_Prop4_02_CosetwiseDescriptionOfPM`
- `DictatorshipTesting.Paper.S04_Prop4_05_SquareEnergyControlsGlobalDegree`
- `DictatorshipTesting.Paper.S05_Lem5_14_MatchingFourierProjections`
-/

/-!
# Definition 4.1: Matching-local degree one and projection

This file collects the local degree-one predicate, the discarded high-degree
energy, the matching-local projection `P_M`, and its squared error.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- A function is locally degree one on every matching cube for `M`. -/
def IsMatchingLocalDegreeOne {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α → ℝ) (M : OrderedMatching α) : Prop :=
  ∀ π : Perm α, cubeHighDegreeEnergy (fun x => F (π * M.tau x)) = 0

/-- Average local high-degree Fourier energy over all base permutations. -/
def matchingLocalHighDegreeEnergy {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α → ℝ) (M : OrderedMatching α) : ℝ :=
  (∑ π : Perm α, cubeHighDegreeEnergy (fun x => F (π * M.tau x))) /
    (Fintype.card (Perm α) : ℝ)

/-- The matching-local projection `P_M`, implemented by taking the degree-at-most-one
Fourier truncation on the matching cube based at the queried permutation and
evaluating it at the cube origin.  Lemma 4.4 proves this agrees with the
representative-independent coset formula. -/
def matchingLocalProjection {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) (F : Perm α → ℝ) : Perm α → ℝ :=
  fun π =>
    cubeLowDegreeOnePart (fun x : FinCube M.edgeCount => F (π * M.tau x))
      (finCubeZero M.edgeCount)

/-- Squared error after removing the matching-local degree-one part. -/
def matchingLocalProjectionError {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α → ℝ) (M : OrderedMatching α) : ℝ :=
  l2DistSq F (matchingLocalProjection M F)

end DictatorshipTesting
