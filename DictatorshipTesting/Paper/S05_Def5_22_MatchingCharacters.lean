import DictatorshipTesting.Paper.Defs
import DictatorshipTesting.Paper.Aux_CubeCharMulSelf
import DictatorshipTesting.Paper.Aux_CubeCharXor

/-
Direct reverse imports (generated):
- `DictatorshipTesting.Paper.S05_Def5_26_MatchingIdempotents`
- `DictatorshipTesting.Paper.S05_Lem5_23_MatchingSubgroupEigenbasis`
- `DictatorshipTesting.Paper.S05_Lem5_24_LocalTruncationOnAMatchingCharacter`
- `DictatorshipTesting.PaperAux`
- `DictatorshipTesting.PaperPlaceholders`
-/

/-!
Paper statement: Definition 5.22 (`def:matching-characters`)
Title in paper: Matching characters.

Status: definition/interface. Re-exports the cube character model currently used for matching-cube
Fourier calculations.
-/

noncomputable section

namespace DictatorshipTesting

/-- Boolean-cube characters take values in `{1,-1}`, hence are nonzero. -/
theorem cubeChar_ne_zero {m : ℕ} (S : Finset (Fin m)) (x : Cube m) :
    cubeChar S x ≠ 0 := by
  unfold cubeChar
  exact Finset.prod_ne_zero_iff.mpr (by
    intro r _hr
    by_cases h : x r <;> simp [h])

/-- Matching-cube character in the current Lean model. -/
abbrev S05_matchingCharacter {m : Nat} (S : Finset (Fin m)) (x : Cube m) : ℝ :=
  cubeChar S x

/-- Weight of a matching-cube character: the size of its support. -/
abbrev S05_matchingCharacterWeight {m : Nat} (S : Finset (Fin m)) : Nat :=
  S.card

/-- Low matching characters are those of weight at most one. -/
def S05_matchingCharacterLow {m : Nat} (S : Finset (Fin m)) : Prop :=
  S05_matchingCharacterWeight S <= 1

/-- High matching characters are those of weight at least two. -/
def S05_matchingCharacterHigh {m : Nat} (S : Finset (Fin m)) : Prop :=
  2 <= S05_matchingCharacterWeight S

instance {m : Nat} (S : Finset (Fin m)) :
    Decidable (S05_matchingCharacterLow S) := by
  unfold S05_matchingCharacterLow S05_matchingCharacterWeight
  infer_instance

instance {m : Nat} (S : Finset (Fin m)) :
    Decidable (S05_matchingCharacterHigh S) := by
  unfold S05_matchingCharacterHigh S05_matchingCharacterWeight
  infer_instance

/-- The empty-support matching character is the constant `1` character. -/
theorem S05_matchingCharacter_empty {m : Nat} (x : Cube m) :
    S05_matchingCharacter (m := m) ∅ x = 1 := by
  simp [S05_matchingCharacter, cubeChar]

/-- Matching characters are never zero. -/
theorem S05_matchingCharacter_ne_zero {m : Nat}
    (S : Finset (Fin m)) (x : Cube m) :
    S05_matchingCharacter S x ≠ 0 := by
  exact cubeChar_ne_zero S x

/-- Matching characters square to `1` pointwise. -/
theorem S05_matchingCharacter_mul_self {m : Nat}
    (S : Finset (Fin m)) (x : Cube m) :
    S05_matchingCharacter S x * S05_matchingCharacter S x = 1 := by
  exact cubeChar_mul_self S x

/-- Matching characters are multiplicative under cube xor. -/
theorem S05_matchingCharacter_cubeXor {m : Nat}
    (S : Finset (Fin m)) (x y : Cube m) :
    S05_matchingCharacter S (cubeXor x y) =
      S05_matchingCharacter S x * S05_matchingCharacter S y := by
  exact cubeChar_cubeXor S x y

/-- The empty-support matching character has weight zero. -/
theorem S05_matchingCharacterWeight_empty {m : Nat} :
    S05_matchingCharacterWeight (m := m) ∅ = 0 := by
  rfl

/-- Empty support is low. -/
theorem S05_matchingCharacterLow_empty {m : Nat} :
    S05_matchingCharacterLow (m := m) ∅ := by
  simp [S05_matchingCharacterLow, S05_matchingCharacterWeight]

/-- Singleton support has weight one. -/
theorem S05_matchingCharacterWeight_singleton {m : Nat} (r : Fin m) :
    S05_matchingCharacterWeight ({r} : Finset (Fin m)) = 1 := by
  simp [S05_matchingCharacterWeight]

/-- Singleton support is low. -/
theorem S05_matchingCharacterLow_singleton {m : Nat} (r : Fin m) :
    S05_matchingCharacterLow ({r} : Finset (Fin m)) := by
  simp [S05_matchingCharacterLow, S05_matchingCharacterWeight]

/-- A matching character cannot be both low and high. -/
theorem S05_not_low_and_high {m : Nat} {S : Finset (Fin m)}
    (hlow : S05_matchingCharacterLow S) (hhigh : S05_matchingCharacterHigh S) :
    False := by
  change S.card <= 1 at hlow
  change 2 <= S.card at hhigh
  omega

/-- Every matching character is either low or high. -/
theorem S05_matchingCharacter_low_or_high {m : Nat} (S : Finset (Fin m)) :
    S05_matchingCharacterLow S ∨ S05_matchingCharacterHigh S := by
  unfold S05_matchingCharacterLow S05_matchingCharacterHigh
    S05_matchingCharacterWeight
  omega

end DictatorshipTesting
