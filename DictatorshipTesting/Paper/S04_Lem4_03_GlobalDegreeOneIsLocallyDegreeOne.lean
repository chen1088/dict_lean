import DictatorshipTesting.Paper.Defs.S04_Def4_01_MatchingLocalDegreeOneAndProjection
import AlgebraicLibrary.BooleanCube.Fourier
import AlgebraicLibrary.BooleanCube.Basic
import DictatorshipTesting.Paper.S03_Lem3_01_DictatorToJunta
import DictatorshipTesting.Paper.S02_Lem2_03_CubeParseval
import DictatorshipTesting.Paper.S04_Int_CubeHighDegreeLinear
import DictatorshipTesting.Paper.S04_Prop4_02_CosetwiseDescriptionOfPM

open AlgebraicLibrary

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S04_Thm4_04_MatchingGap`
- `DictatorshipTesting.Paper.S05_Prop5_16_AveragedRejectionOnYoungBlocks`
-/

/-!
# Lemma 4.3: Global degree one is locally degree one

The coordinate functions spanning `U1` restrict to degree at most one on every
matching cube, so `U1` is fixed by every matching-local projection.
-/

namespace DictatorshipTesting

/-- If a function is invariant under flipping a coordinate in the character
support, then the corresponding Fourier coefficient is zero. -/
theorem cubeFourierCoeff_eq_zero_of_cubeFlip_invariant {m : ℕ}
    (g : FinCube m → ℝ) {S : Finset (Fin m)} {r : Fin m}
    (hr : r ∈ S) (hflip : ∀ x, g (cubeFlip r x) = g x) :
    cubeFourierCoeff g S = 0 := by
  classical
  unfold cubeFourierCoeff cubeExpectation
  have hsum : (∑ x : FinCube m, g x * cubeChar S x) = 0 := by
    simpa using
      (Finset.sum_involution
        (s := (Finset.univ : Finset (FinCube m)))
        (f := fun x => g x * cubeChar S x)
        (g := fun x _ => cubeFlip r x)
        (by
          intro x _h
          rw [hflip x, cubeChar_cubeFlip S r hr x]
          ring)
        (by
          intro x _h _hmem hfix
          have hcoord := congr_fun hfix r
          by_cases hx : x r <;> simp [cubeFlip, hx] at hcoord)
        (by
          intro x _h
          simp)
        (by
          intro x _h
          exact cubeFlip_involutive r x))
  simp [hsum]

theorem cubeFourierCoeff_bool_constant_eq_zero_of_two_le_card {m : ℕ}
    (g : FinCube m → Bool) (hg : IsCubeConstant g)
    {S : Finset (Fin m)} (hS : 2 ≤ S.card) :
    cubeFourierCoeff (fun x => boolToReal (g x)) S = 0 := by
  have hpos : 0 < S.card := by omega
  rcases (Finset.card_pos.mp hpos) with ⟨r, hr⟩
  apply cubeFourierCoeff_eq_zero_of_cubeFlip_invariant
  · exact hr
  · intro x
    rw [hg (cubeFlip r x) x]

theorem exists_mem_ne_of_two_le_card {m : ℕ} (S : Finset (Fin m))
    (r : Fin m) (hS : 2 ≤ S.card) :
    ∃ t, t ∈ S ∧ t ≠ r := by
  have hlt : 1 < S.card := by omega
  rcases (Finset.one_lt_card.mp hlt) with ⟨a, ha, b, hb, hab⟩
  by_cases har : a = r
  · refine ⟨b, hb, ?_⟩
    intro hbr
    exact hab (har.trans hbr.symm)
  · exact ⟨a, ha, har⟩

theorem cubeFourierCoeff_bool_juntaAt_eq_zero_of_two_le_card {m : ℕ}
    (g : FinCube m → Bool) {r : Fin m} (hg : IsCubeJuntaAt g r)
    {S : Finset (Fin m)} (hS : 2 ≤ S.card) :
    cubeFourierCoeff (fun x => boolToReal (g x)) S = 0 := by
  rcases exists_mem_ne_of_two_le_card S r hS with ⟨t, htS, htr⟩
  apply cubeFourierCoeff_eq_zero_of_cubeFlip_invariant
  · exact htS
  · intro x
    have hcoord : (cubeFlip t x) r = x r := by
      simp [cubeFlip, htr.symm]
    exact congrArg boolToReal (hg (cubeFlip t x) x hcoord)

/-- A Boolean one-junta has no Fourier energy in levels at least two. -/
theorem cubeHighDegreeEnergy_boolToReal_eq_zero_of_oneJunta {m : ℕ}
    (g : FinCube m → Bool) (hg : IsCubeOneJunta g) :
    cubeHighDegreeEnergy (fun x => boolToReal (g x)) = 0 := by
  classical
  unfold cubeHighDegreeEnergy
  apply Finset.sum_eq_zero
  intro S hS
  have hcard : 2 ≤ S.card := (Finset.mem_filter.mp hS).2
  rcases hg with hconst | hjunta
  · simp [cubeFourierCoeff_bool_constant_eq_zero_of_two_le_card g hconst hcard]
  · rcases hjunta with ⟨r, hr⟩
    simp [cubeFourierCoeff_bool_juntaAt_eq_zero_of_two_le_card g hr hcard]

/-- Lemma 4.3, `lem:tij-local-degree`: basic indicators have local degree at most one. -/
theorem S04_Lem4_03_TijLocalDegree {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) (i j : α) :
    IsMatchingLocalDegreeOne (oneCosetReal i j) M := by
  intro π
  let f : BoolFn α := fun ρ => decide (ρ i = j)
  have hf : IsImageDictator f := by
    refine ⟨i, fun a => decide (a = j), ?_⟩
    intro ρ
    rfl
  have hjunta : IsCubeOneJunta (matchingCubeRestriction f M π) :=
    S03_Lem3_01_ImageDictatorToJunta f hf M π
  have henergy :
      cubeHighDegreeEnergy
          (fun x => boolToReal (matchingCubeRestriction f M π x)) = 0 :=
    cubeHighDegreeEnergy_boolToReal_eq_zero_of_oneJunta
      (matchingCubeRestriction f M π) hjunta
  convert henergy using 2
  ext x
  simp [f, matchingCubeRestriction, oneCosetReal, boolToReal]

/-- The zero cube function has no high-degree Fourier energy. -/
theorem cubeHighDegreeEnergy_zero (m : ℕ) :
    cubeHighDegreeEnergy (fun _ : FinCube m => (0 : ℝ)) = 0 := by
  apply cubeHighDegreeEnergy_eq_zero_of_forall_highDegree_coeff_zero
  intro S _hS
  unfold cubeFourierCoeff cubeExpectation
  simp

/-- The zero function is matching-local degree one. -/
theorem IsMatchingLocalDegreeOne_zero {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) :
    IsMatchingLocalDegreeOne (fun _ : Perm α => (0 : ℝ)) M := by
  intro π
  simpa using cubeHighDegreeEnergy_zero M.edgeCount

/-- Matching-local degree one is closed under addition. -/
theorem IsMatchingLocalDegreeOne_add {α : Type*} [Fintype α] [DecidableEq α]
    {F G : Perm α → ℝ} {M : OrderedMatching α}
    (hF : IsMatchingLocalDegreeOne F M)
    (hG : IsMatchingLocalDegreeOne G M) :
    IsMatchingLocalDegreeOne (F + G) M := by
  intro π
  simpa [Pi.add_apply] using cubeHighDegreeEnergy_add_eq_zero (hF π) (hG π)

/-- Matching-local degree one is closed under scalar multiplication. -/
theorem IsMatchingLocalDegreeOne_smul {α : Type*} [Fintype α] [DecidableEq α]
    (a : ℝ) {F : Perm α → ℝ} {M : OrderedMatching α}
    (hF : IsMatchingLocalDegreeOne F M) :
    IsMatchingLocalDegreeOne (a • F) M := by
  intro π
  simpa [Pi.smul_apply, smul_eq_mul] using
    cubeHighDegreeEnergy_smul_eq_zero a (hF π)

/-- Lemma 4.3, `cor:U1-local`: `U_1` is contained in each local degree-one space. -/
theorem S04_Lem4_03_GlobalDegreeOneIsLocallyDegreeOne {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) (F : Perm α → ℝ) (hF : F ∈ U1 α) :
    IsMatchingLocalDegreeOne F M ∧ matchingLocalProjection M F = F := by
  have hlocal : IsMatchingLocalDegreeOne F M := by
    unfold U1 at hF
    refine Submodule.span_induction
      (p := fun F _ => IsMatchingLocalDegreeOne F M)
      ?mem ?zero ?add ?smul hF
    · intro G hG
      rcases hG with ⟨ij, rfl⟩
      exact S04_Lem4_03_TijLocalDegree M ij.1 ij.2
    · exact IsMatchingLocalDegreeOne_zero M
    · intro G H _hGmem _hHmem hG hH
      exact IsMatchingLocalDegreeOne_add hG hH
    · intro a G _hGmem hG
      exact IsMatchingLocalDegreeOne_smul a hG
  exact ⟨hlocal, (S04_Prop4_02_fixedSpace F M).2 F hlocal⟩

end DictatorshipTesting
