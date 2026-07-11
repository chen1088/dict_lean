import DictatorshipTesting.Paper.Defs.S04_Def4_01a_IsMatchingLocalDegreeOne
import DictatorshipTesting.Paper.S02_Int_CubeCharFlip
import DictatorshipTesting.Paper.S02_Int_CubeFlipInvolutive
import DictatorshipTesting.Paper.S03_Lem3_01_DictatorToJunta

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S04_Cor4_07_U1Local`
-/


/-!
# Lemma 4.6: A basic indicator has local degree at most one

This is `lem:tij-local-degree` from `dictatorship_testing_soda27_latest.tex`.
-/

namespace DictatorshipTesting

/-- If a function is invariant under flipping a coordinate in the character
support, then the corresponding Fourier coefficient is zero. -/
theorem cubeFourierCoeff_eq_zero_of_cubeFlip_invariant {m : ℕ}
    (g : Cube m → ℝ) {S : Finset (Fin m)} {r : Fin m}
    (hr : r ∈ S) (hflip : ∀ x, g (cubeFlip r x) = g x) :
    cubeFourierCoeff g S = 0 := by
  classical
  unfold cubeFourierCoeff cubeExpectation
  have hsum : (∑ x : Cube m, g x * cubeChar S x) = 0 := by
    simpa using
      (Finset.sum_involution
        (s := (Finset.univ : Finset (Cube m)))
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
    (g : Cube m → Bool) (hg : IsCubeConstant g)
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
    (g : Cube m → Bool) {r : Fin m} (hg : IsCubeJuntaAt g r)
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
    (g : Cube m → Bool) (hg : IsCubeOneJunta g) :
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

/-- Lemma 4.6, `lem:tij-local-degree`: basic indicators have local degree at most one. -/
theorem S04_Lem4_06_TijLocalDegree {α : Type*} [Fintype α] [DecidableEq α]
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

end DictatorshipTesting
