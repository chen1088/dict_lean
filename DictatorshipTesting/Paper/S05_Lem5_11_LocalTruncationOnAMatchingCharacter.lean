import DictatorshipTesting.Paper.S04_Int_CubeLowDegreeError
import DictatorshipTesting.Paper.S04_Int_MatchingLocalProjection
import DictatorshipTesting.Paper.Defs.S05_Def5_15_MatchingCharacters

/-
Direct reverse imports:
- `DictatorshipTesting`
-/


/-!
Paper statement: Lemma 5.11 (`lem:PM-character-projection`)
Title in paper: Local truncation on a matching character.

Status: proven. Proved below by elementary matching-cube Fourier calculations.
-/

/-!
# Local character projection

This file proves the elementary Fourier statement behind the local matching
projection: on a matching cube, `P_M` keeps cube characters of degree `0` or
`1` and kills cube characters of degree at least `2`.
-/

noncomputable section

namespace DictatorshipTesting

/-- The degree-at-most-one cube projection preserves low-degree characters. -/
theorem cubeLowDegreeOnePart_cubeChar_of_card_le_one {m : ℕ}
    {S : Finset (Fin m)} (hS : S.card ≤ 1) :
    cubeLowDegreeOnePart (fun x : Cube m => cubeChar S x) =
      fun x : Cube m => cubeChar S x := by
  exact
    cubeLowDegreeOnePart_eq_self_of_cubeHighDegreeEnergy_eq_zero
      (cubeHighDegreeEnergy_cubeChar_eq_zero_of_card_le_one hS)

/-- The degree-at-most-one cube projection kills high-degree characters. -/
theorem cubeLowDegreeOnePart_cubeChar_of_two_le_card {m : ℕ}
    {S : Finset (Fin m)} (hS : 2 ≤ S.card) :
    cubeLowDegreeOnePart (fun x : Cube m => cubeChar S x) =
      fun _ : Cube m => 0 := by
  classical
  funext x
  unfold cubeLowDegreeOnePart
  apply Finset.sum_eq_zero
  intro T hT
  have hTle : T.card ≤ 1 := (Finset.mem_filter.mp hT).2
  have hne : S ≠ T := by
    intro hST
    have : S.card ≤ 1 := by simpa [hST] using hTle
    omega
  simp [cubeFourierCoeff_cubeChar, hne]

/-- On a local matching cube, `P_M` preserves local characters of weight `0` or
`1`. -/
theorem matchingLocalProjection_preserves_low_local_char {α : Type*}
    [Fintype α] [DecidableEq α] (M : OrderedMatching α)
    (F : Perm α → ℝ) (π : Perm α) {S : Finset (Fin M.edgeCount)}
    (hS : S.card ≤ 1)
    (hlocal : ∀ x : Cube M.edgeCount, F (π * M.tau x) = cubeChar S x)
    (x : Cube M.edgeCount) :
    matchingLocalProjection M F (π * M.tau x) = F (π * M.tau x) := by
  have hg :
      (fun y : Cube M.edgeCount => F (π * M.tau y)) =
        fun y : Cube M.edgeCount => cubeChar S y := by
    funext y
    exact hlocal y
  rw [matchingLocalProjection_apply_mul_tau, hg,
    cubeLowDegreeOnePart_cubeChar_of_card_le_one hS]
  exact (hlocal x).symm

/-- On a local matching cube, `P_M` kills local characters of weight at least
`2`. -/
theorem matchingLocalProjection_kills_high_local_char {α : Type*}
    [Fintype α] [DecidableEq α] (M : OrderedMatching α)
    (F : Perm α → ℝ) (π : Perm α) {S : Finset (Fin M.edgeCount)}
    (hS : 2 ≤ S.card)
    (hlocal : ∀ x : Cube M.edgeCount, F (π * M.tau x) = cubeChar S x)
    (x : Cube M.edgeCount) :
    matchingLocalProjection M F (π * M.tau x) = 0 := by
  have hg :
      (fun y : Cube M.edgeCount => F (π * M.tau y)) =
        fun y : Cube M.edgeCount => cubeChar S y := by
    funext y
    exact hlocal y
  rw [matchingLocalProjection_apply_mul_tau, hg,
    cubeLowDegreeOnePart_cubeChar_of_two_le_card hS]

/-- Lemma 5.24, matching-character vocabulary: local truncation preserves low
matching characters. -/
theorem S05_Lem5_11_cubeLowDegreeOnePart_matchingCharacter_of_low {m : ℕ}
    {S : Finset (Fin m)} (hS : S05_matchingCharacterLow S) :
    cubeLowDegreeOnePart (fun x : Cube m => S05_matchingCharacter S x) =
      fun x : Cube m => S05_matchingCharacter S x := by
  exact cubeLowDegreeOnePart_cubeChar_of_card_le_one hS

/-- Lemma 5.24, matching-character vocabulary: local truncation kills high
matching characters. -/
theorem S05_Lem5_11_cubeLowDegreeOnePart_matchingCharacter_of_high {m : ℕ}
    {S : Finset (Fin m)} (hS : S05_matchingCharacterHigh S) :
    cubeLowDegreeOnePart (fun x : Cube m => S05_matchingCharacter S x) =
      fun _ : Cube m => 0 := by
  exact cubeLowDegreeOnePart_cubeChar_of_two_le_card hS

/-- Lemma 5.24, matching-character vocabulary: every matching character is
either preserved by the local truncation or killed by it. -/
theorem S05_Lem5_11_cubeLowDegreeOnePart_matchingCharacter_preserved_or_killed
    {m : ℕ} (S : Finset (Fin m)) :
    (cubeLowDegreeOnePart (fun x : Cube m => S05_matchingCharacter S x) =
        fun x : Cube m => S05_matchingCharacter S x) ∨
      (cubeLowDegreeOnePart (fun x : Cube m => S05_matchingCharacter S x) =
        fun _ : Cube m => 0) := by
  rcases S05_matchingCharacter_low_or_high S with hlow | hhigh
  · exact Or.inl (S05_Lem5_11_cubeLowDegreeOnePart_matchingCharacter_of_low hlow)
  · exact Or.inr (S05_Lem5_11_cubeLowDegreeOnePart_matchingCharacter_of_high hhigh)

/-- Lemma 5.24, matching-character vocabulary: `P_M` preserves low local
matching characters. -/
theorem S05_Lem5_11_matchingLocalProjection_preserves_low_matchingCharacter
    {α : Type*} [Fintype α] [DecidableEq α] (M : OrderedMatching α)
    (F : Perm α → ℝ) (π : Perm α) {S : Finset (Fin M.edgeCount)}
    (hS : S05_matchingCharacterLow S)
    (hlocal : ∀ x : Cube M.edgeCount,
      F (π * M.tau x) = S05_matchingCharacter S x)
    (x : Cube M.edgeCount) :
    matchingLocalProjection M F (π * M.tau x) = F (π * M.tau x) := by
  exact matchingLocalProjection_preserves_low_local_char M F π hS hlocal x

/-- Lemma 5.24, matching-character vocabulary: `P_M` kills high local matching
characters. -/
theorem S05_Lem5_11_matchingLocalProjection_kills_high_matchingCharacter
    {α : Type*} [Fintype α] [DecidableEq α] (M : OrderedMatching α)
    (F : Perm α → ℝ) (π : Perm α) {S : Finset (Fin M.edgeCount)}
    (hS : S05_matchingCharacterHigh S)
    (hlocal : ∀ x : Cube M.edgeCount,
      F (π * M.tau x) = S05_matchingCharacter S x)
    (x : Cube M.edgeCount) :
    matchingLocalProjection M F (π * M.tau x) = 0 := by
  exact matchingLocalProjection_kills_high_local_char M F π hS hlocal x

end DictatorshipTesting
