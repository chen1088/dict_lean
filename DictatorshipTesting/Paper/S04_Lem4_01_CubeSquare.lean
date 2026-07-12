import DictatorshipTesting.Paper.Defs.S03_IntDef_CubeSquareEnergy
import DictatorshipTesting.Paper.S02_Int_CubeFourierTranslate
import DictatorshipTesting.Paper.S04_Int_CubeHighDegreeLinear
import DictatorshipTesting.Paper.S02_Lem2_03_CubeParsevalIdentity

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S04_Prop4_08_SquareEnergyControlsGlobalDegree`
-/


/-!
# Lemma 4.1: Square test detects Fourier weight at least two

This is `lem:cube-square` from `dictatorship_testing_stoc27_latest.tex`.
The dedicated spectral-formula and color-counting helpers are kept here because
this paper lemma is their only direct user.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Translating a cube function on the right by xor has the same Fourier effect
as translating on the left. -/
theorem cubeFourierCoeff_xor_right {m : ℕ} (g : Cube m → ℝ)
    (z : Cube m) (S : Finset (Fin m)) :
    cubeFourierCoeff (fun y => g (cubeXor y z)) S =
      cubeChar S z * cubeFourierCoeff g S := by
  simpa [cubeXor_comm] using cubeFourierCoeff_xor_left g z S

/-- The Fourier coefficient of a mixed cube difference is multiplied by the
corresponding character difference factors. -/
theorem cubeFourierCoeff_cubeDelta {m : ℕ} (g : Cube m → ℝ)
    (u v : Cube m) (S : Finset (Fin m)) :
    cubeFourierCoeff (fun x => cubeDelta g x u v) S =
      cubeFourierCoeff g S * (1 - cubeChar S u) * (1 - cubeChar S v) := by
  unfold cubeDelta
  have hlast :
      cubeFourierCoeff
          (fun x : Cube m => g (cubeXor (cubeXor x u) v)) S =
        cubeChar S u * cubeChar S v * cubeFourierCoeff g S := by
    calc
      cubeFourierCoeff
          (fun x : Cube m => g (cubeXor (cubeXor x u) v)) S
          =
          cubeFourierCoeff
            (fun x : Cube m => g (cubeXor x (cubeXor u v))) S := by
            congr 1
            ext x
            rw [cubeXor_assoc]
      _ = cubeChar S (cubeXor u v) * cubeFourierCoeff g S := by
            rw [cubeFourierCoeff_xor_right]
      _ = cubeChar S u * cubeChar S v * cubeFourierCoeff g S := by
            rw [cubeChar_cubeXor]
  calc
    cubeFourierCoeff
        (fun x : Cube m =>
          g x - g (cubeXor x u) - g (cubeXor x v) +
            g (cubeXor (cubeXor x u) v)) S
        =
        cubeFourierCoeff
          (fun x : Cube m =>
            g x + (-1) * g (cubeXor x u) +
              ((-1) * g (cubeXor x v) +
                g (cubeXor (cubeXor x u) v))) S := by
          congr 1
          ext x
          ring
    _ =
        cubeFourierCoeff g S +
          cubeFourierCoeff (fun x : Cube m => (-1) * g (cubeXor x u)) S +
            (cubeFourierCoeff (fun x : Cube m => (-1) * g (cubeXor x v)) S +
              cubeFourierCoeff
                (fun x : Cube m => g (cubeXor (cubeXor x u) v)) S) := by
          rw [cubeFourierCoeff_add]
          rw [cubeFourierCoeff_add]
          rw [cubeFourierCoeff_add]
    _ =
        cubeFourierCoeff g S +
          (-1) * (cubeChar S u * cubeFourierCoeff g S) +
            ((-1) * (cubeChar S v * cubeFourierCoeff g S) +
              cubeChar S u * cubeChar S v * cubeFourierCoeff g S) := by
          rw [cubeFourierCoeff_smul, cubeFourierCoeff_smul]
          rw [cubeFourierCoeff_xor_right, cubeFourierCoeff_xor_right, hlast]
    _ = cubeFourierCoeff g S * (1 - cubeChar S u) * (1 - cubeChar S v) := by
          ring

/-- For fixed directions, Parseval expresses the square-difference energy as a
Fourier coefficient sum with the usual multiplier. -/
theorem cubeDelta_parseval {m : ℕ} (g : Cube m → ℝ) (u v : Cube m) :
    cubeExpectation (fun x : Cube m => (cubeDelta g x u v) ^ (2 : ℕ)) =
      ∑ S : Finset (Fin m),
        (cubeFourierCoeff g S * (1 - cubeChar S u) *
          (1 - cubeChar S v)) ^ (2 : ℕ) := by
  calc
    cubeExpectation (fun x : Cube m => (cubeDelta g x u v) ^ (2 : ℕ))
        =
        ∑ S : Finset (Fin m),
          (cubeFourierCoeff (fun x : Cube m => cubeDelta g x u v) S) ^ (2 : ℕ) := by
          exact S02_Lem2_03_cubeParseval_identity m (fun x : Cube m => cubeDelta g x u v)
    _ =
        ∑ S : Finset (Fin m),
          (cubeFourierCoeff g S * (1 - cubeChar S u) *
            (1 - cubeChar S v)) ^ (2 : ℕ) := by
          apply Finset.sum_congr rfl
          intro S _hS
          rw [cubeFourierCoeff_cubeDelta]

/-- The square-test energy can be viewed as first averaging over the cube for
each color choice, and then averaging over colors. -/
theorem cubeSquareEnergy_eq_color_average {m : ℕ} (g : Cube m → ℝ) :
    cubeSquareEnergy g =
      (∑ c : CubeDirectionColor m,
        cubeExpectation
          (fun x : Cube m =>
            (cubeDelta g x (cubeColorU c) (cubeColorV c)) ^ (2 : ℕ))) /
        (Fintype.card (CubeDirectionColor m) : ℝ) := by
  unfold cubeSquareEnergy cubeExpectation
  calc
    (∑ x : Cube m,
        (∑ c : CubeDirectionColor m,
          (cubeDelta g x (cubeColorU c) (cubeColorV c)) ^ (2 : ℕ)) /
            (Fintype.card (CubeDirectionColor m) : ℝ)) /
      (Fintype.card (Cube m) : ℝ)
        =
        ((∑ x : Cube m,
          ∑ c : CubeDirectionColor m,
            (cubeDelta g x (cubeColorU c) (cubeColorV c)) ^ (2 : ℕ)) /
            (Fintype.card (CubeDirectionColor m) : ℝ)) /
          (Fintype.card (Cube m) : ℝ) := by
          rw [← Finset.sum_div]
    _ =
        ((∑ c : CubeDirectionColor m,
          ∑ x : Cube m,
            (cubeDelta g x (cubeColorU c) (cubeColorV c)) ^ (2 : ℕ)) /
            (Fintype.card (CubeDirectionColor m) : ℝ)) /
          (Fintype.card (Cube m) : ℝ) := by
          rw [Finset.sum_comm]
    _ =
        ((∑ c : CubeDirectionColor m,
          ∑ x : Cube m,
            (cubeDelta g x (cubeColorU c) (cubeColorV c)) ^ (2 : ℕ)) /
            (Fintype.card (Cube m) : ℝ)) /
          (Fintype.card (CubeDirectionColor m) : ℝ) := by
          ring_nf
    _ =
        (∑ c : CubeDirectionColor m,
          (∑ x : Cube m,
            (cubeDelta g x (cubeColorU c) (cubeColorV c)) ^ (2 : ℕ)) /
              (Fintype.card (Cube m) : ℝ)) /
            (Fintype.card (CubeDirectionColor m) : ℝ) := by
          rw [Finset.sum_div]

/-- The average square-test multiplier for one cube character. -/
def cubeColorMultiplierAverage {m : ℕ} (S : Finset (Fin m)) : ℝ :=
  (∑ c : CubeDirectionColor m,
    ((1 - cubeChar S (cubeColorU c)) *
      (1 - cubeChar S (cubeColorV c))) ^ (2 : ℕ)) /
    (Fintype.card (CubeDirectionColor m) : ℝ)

/-- The cube square-test energy decomposes diagonally in the Fourier basis. -/
theorem cubeSquareEnergy_spectral_formula {m : ℕ} (g : Cube m → ℝ) :
    cubeSquareEnergy g =
      ∑ S : Finset (Fin m),
        (cubeFourierCoeff g S) ^ (2 : ℕ) * cubeColorMultiplierAverage S := by
  rw [cubeSquareEnergy_eq_color_average]
  unfold cubeColorMultiplierAverage
  calc
    (∑ c : CubeDirectionColor m,
        cubeExpectation
          (fun x : Cube m =>
            (cubeDelta g x (cubeColorU c) (cubeColorV c)) ^ (2 : ℕ))) /
        (Fintype.card (CubeDirectionColor m) : ℝ)
        =
        (∑ c : CubeDirectionColor m,
          ∑ S : Finset (Fin m),
            (cubeFourierCoeff g S * (1 - cubeChar S (cubeColorU c)) *
              (1 - cubeChar S (cubeColorV c))) ^ (2 : ℕ)) /
          (Fintype.card (CubeDirectionColor m) : ℝ) := by
          congr 1
          apply Finset.sum_congr rfl
          intro c _
          rw [cubeDelta_parseval]
    _ =
        (∑ S : Finset (Fin m),
          ∑ c : CubeDirectionColor m,
            (cubeFourierCoeff g S * (1 - cubeChar S (cubeColorU c)) *
              (1 - cubeChar S (cubeColorV c))) ^ (2 : ℕ)) /
          (Fintype.card (CubeDirectionColor m) : ℝ) := by
          rw [Finset.sum_comm]
    _ =
        ∑ S : Finset (Fin m),
          ((∑ c : CubeDirectionColor m,
            (cubeFourierCoeff g S * (1 - cubeChar S (cubeColorU c)) *
              (1 - cubeChar S (cubeColorV c))) ^ (2 : ℕ)) /
            (Fintype.card (CubeDirectionColor m) : ℝ)) := by
          rw [Finset.sum_div]
    _ =
        ∑ S : Finset (Fin m),
          (cubeFourierCoeff g S) ^ (2 : ℕ) *
            ((∑ c : CubeDirectionColor m,
              ((1 - cubeChar S (cubeColorU c)) *
                (1 - cubeChar S (cubeColorV c))) ^ (2 : ℕ)) /
              (Fintype.card (CubeDirectionColor m) : ℝ)) := by
          apply Finset.sum_congr rfl
          intro S _
          calc
            (∑ c : CubeDirectionColor m,
              (cubeFourierCoeff g S * (1 - cubeChar S (cubeColorU c)) *
                (1 - cubeChar S (cubeColorV c))) ^ (2 : ℕ)) /
                (Fintype.card (CubeDirectionColor m) : ℝ)
                =
                (∑ c : CubeDirectionColor m,
                  (cubeFourierCoeff g S) ^ (2 : ℕ) *
                    ((1 - cubeChar S (cubeColorU c)) *
                      (1 - cubeChar S (cubeColorV c))) ^ (2 : ℕ)) /
                  (Fintype.card (CubeDirectionColor m) : ℝ) := by
                  congr 1
                  apply Finset.sum_congr rfl
                  intro c _
                  ring
            _ =
                ((cubeFourierCoeff g S) ^ (2 : ℕ) *
                  (∑ c : CubeDirectionColor m,
                    ((1 - cubeChar S (cubeColorU c)) *
                      (1 - cubeChar S (cubeColorV c))) ^ (2 : ℕ))) /
                  (Fintype.card (CubeDirectionColor m) : ℝ) := by
                  congr 1
                  rw [Finset.mul_sum]
            _ =
                (cubeFourierCoeff g S) ^ (2 : ℕ) *
                  ((∑ c : CubeDirectionColor m,
                    ((1 - cubeChar S (cubeColorU c)) *
                      (1 - cubeChar S (cubeColorV c))) ^ (2 : ℕ)) /
                    (Fintype.card (CubeDirectionColor m) : ℝ)) := by
                  ring

/-- The contribution of one color to the `U`-direction character. -/
def cubeColorSignU (a : Fin 3) : ℝ :=
  if a = (1 : Fin 3) then (-1 : ℝ) else 1

/-- The contribution of one color to the `V`-direction character. -/
def cubeColorSignV (a : Fin 3) : ℝ :=
  if a = (2 : Fin 3) then (-1 : ℝ) else 1

/-- A coloring together with two replacement colors. -/
abbrev CubeColorOverwriteTriple (m : ℕ) :=
  CubeDirectionColor m × Fin 3 × Fin 3

/-- Overwrite two distinct coordinates, remembering the previous two colors.

This is an involution, so it gives the counting identity used below. -/
def cubeColorOverwriteEquiv {m : ℕ} (r s : Fin m) (hrs : r ≠ s) :
    CubeColorOverwriteTriple m ≃ CubeColorOverwriteTriple m where
  toFun x :=
    (Function.update (Function.update x.1 r x.2.1) s x.2.2, (x.1 r, x.1 s))
  invFun x :=
    (Function.update (Function.update x.1 r x.2.1) s x.2.2, (x.1 r, x.1 s))
  left_inv := by
    intro x
    cases x with
    | mk c pq =>
      cases pq with
      | mk p q =>
        have hsr : s ≠ r := fun h => hrs h.symm
        ext i <;> simp [Function.update] <;> split_ifs <;> simp_all
  right_inv := by
    intro x
    cases x with
    | mk c pq =>
      cases pq with
      | mk p q =>
        have hsr : s ≠ r := fun h => hrs h.symm
        ext i <;> simp [Function.update] <;> split_ifs <;> simp_all

/-- Summing over a base coloring and two overwritten colors counts each final
coloring exactly nine times. -/
theorem cubeColor_sum_update_update {m : ℕ} (r s : Fin m) (hrs : r ≠ s)
    (f : CubeDirectionColor m → ℝ) :
    (∑ c : CubeDirectionColor m,
      ∑ p : Fin 3,
        ∑ q : Fin 3,
          f (Function.update (Function.update c r p) s q)) =
      (9 : ℝ) * ∑ c : CubeDirectionColor m, f c := by
  let e := cubeColorOverwriteEquiv r s hrs
  have hprod :
      (∑ x : CubeColorOverwriteTriple m,
          f (Function.update (Function.update x.1 r x.2.1) s x.2.2)) =
        (∑ c : CubeDirectionColor m,
          ∑ p : Fin 3,
            ∑ q : Fin 3,
              f (Function.update (Function.update c r p) s q)) := by
    calc
      (∑ x : CubeColorOverwriteTriple m,
          f (Function.update (Function.update x.1 r x.2.1) s x.2.2))
          = ∑ c : CubeDirectionColor m,
              ∑ pq : Fin 3 × Fin 3,
                f (Function.update (Function.update c r pq.1) s pq.2) := by
              exact Fintype.sum_prod_type' (fun c (pq : Fin 3 × Fin 3) =>
                f (Function.update (Function.update c r pq.1) s pq.2))
      _ = (∑ c : CubeDirectionColor m,
          ∑ p : Fin 3,
            ∑ q : Fin 3,
              f (Function.update (Function.update c r p) s q)) := by
          apply Finset.sum_congr rfl
          intro c _
          exact Fintype.sum_prod_type' (fun p q =>
            f (Function.update (Function.update c r p) s q))
  rw [← hprod]
  calc
    (∑ x : CubeColorOverwriteTriple m,
        f (Function.update (Function.update x.1 r x.2.1) s x.2.2))
        = ∑ x : CubeColorOverwriteTriple m, f (e x).1 := by
          rfl
    _ = ∑ x : CubeColorOverwriteTriple m, f x.1 := by
          exact Equiv.sum_comp e (fun x : CubeColorOverwriteTriple m => f x.1)
    _ = (9 : ℝ) * ∑ c : CubeDirectionColor m, f c := by
          calc
            (∑ x : CubeColorOverwriteTriple m, f x.1)
              = ∑ c : CubeDirectionColor m,
                  ∑ pq : Fin 3 × Fin 3, f c := by
                  exact Fintype.sum_prod_type'
                    (fun c (_pq : Fin 3 × Fin 3) => f c)
            _ = ∑ c : CubeDirectionColor m,
                  ∑ p : Fin 3,
                    ∑ _q : Fin 3, f c := by
                  apply Finset.sum_congr rfl
                  intro c _
                  exact Fintype.sum_prod_type'
                    (fun (_p : Fin 3) (_q : Fin 3) => f c)
            _ = (9 : ℝ) * ∑ c : CubeDirectionColor m, f c := by
                  simp [Finset.mul_sum]
                  ring_nf

/-- The two-coordinate color enumeration that gives the `32` numerator. -/
theorem cubeColor_twoCoord_sum_lower {A B : ℝ}
    (hA : A = 1 ∨ A = -1) (hB : B = 1 ∨ B = -1) :
    (32 : ℝ) ≤
      ∑ p : Fin 3,
        ∑ q : Fin 3,
          ((1 - A * cubeColorSignU p * cubeColorSignU q) *
            (1 - B * cubeColorSignV p * cubeColorSignV q)) ^ (2 : ℕ) := by
  rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
  all_goals
    simp_rw [Fin.sum_univ_three]
    simp [cubeColorSignU, cubeColorSignV]
    norm_num

/-- The `U`-character after overwriting two support coordinates factors into
the remaining character times the two local color signs. -/
theorem cubeChar_cubeColorU_update_update {m : ℕ} (S : Finset (Fin m))
    {r s : Fin m} (hr : r ∈ S) (hs : s ∈ S) (hrs : r ≠ s)
    (c : CubeDirectionColor m) (p q : Fin 3) :
    cubeChar S (cubeColorU (Function.update (Function.update c r p) s q)) =
      cubeChar ((S.erase r).erase s) (cubeColorU c) *
        cubeColorSignU p * cubeColorSignU q := by
  let d : CubeDirectionColor m := Function.update (Function.update c r p) s q
  let f : Fin m → ℝ := fun i => if cubeColorU d i then (-1 : ℝ) else 1
  have hs_erased : s ∈ S.erase r := by
    exact Finset.mem_erase.mpr ⟨fun h => hrs h.symm, hs⟩
  have hprod_rest :
      (∏ i ∈ (S.erase r).erase s, f i) =
        cubeChar ((S.erase r).erase s) (cubeColorU c) := by
    unfold cubeChar
    apply Finset.prod_congr rfl
    intro i hi
    have his : i ≠ s := (Finset.mem_erase.mp hi).1
    have hir : i ≠ r := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    simp [f, d, cubeColorU, Function.update, hir, his]
  have hfr : f r = cubeColorSignU p := by
    simp [f, d, cubeColorU, cubeColorSignU, Function.update, hrs]
  have hfs : f s = cubeColorSignU q := by
    simp [f, d, cubeColorU, cubeColorSignU, Function.update]
  have hS :
      (∏ i ∈ S, f i) =
        cubeChar ((S.erase r).erase s) (cubeColorU c) *
          cubeColorSignU p * cubeColorSignU q := by
    calc
      (∏ i ∈ S, f i)
          = (∏ i ∈ S.erase r, f i) * f r := by
              rw [Finset.prod_erase_mul S f hr]
      _ = ((∏ i ∈ (S.erase r).erase s, f i) * f s) * f r := by
              rw [Finset.prod_erase_mul (S.erase r) f hs_erased]
      _ = cubeChar ((S.erase r).erase s) (cubeColorU c) *
            cubeColorSignU p * cubeColorSignU q := by
              rw [hprod_rest, hfr, hfs]
              ring
  unfold cubeChar
  exact hS

/-- The `V`-character after overwriting two support coordinates factors into
the remaining character times the two local color signs. -/
theorem cubeChar_cubeColorV_update_update {m : ℕ} (S : Finset (Fin m))
    {r s : Fin m} (hr : r ∈ S) (hs : s ∈ S) (hrs : r ≠ s)
    (c : CubeDirectionColor m) (p q : Fin 3) :
    cubeChar S (cubeColorV (Function.update (Function.update c r p) s q)) =
      cubeChar ((S.erase r).erase s) (cubeColorV c) *
        cubeColorSignV p * cubeColorSignV q := by
  let d : CubeDirectionColor m := Function.update (Function.update c r p) s q
  let f : Fin m → ℝ := fun i => if cubeColorV d i then (-1 : ℝ) else 1
  have hs_erased : s ∈ S.erase r := by
    exact Finset.mem_erase.mpr ⟨fun h => hrs h.symm, hs⟩
  have hprod_rest :
      (∏ i ∈ (S.erase r).erase s, f i) =
        cubeChar ((S.erase r).erase s) (cubeColorV c) := by
    unfold cubeChar
    apply Finset.prod_congr rfl
    intro i hi
    have his : i ≠ s := (Finset.mem_erase.mp hi).1
    have hir : i ≠ r := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    simp [f, d, cubeColorV, Function.update, hir, his]
  have hfr : f r = cubeColorSignV p := by
    simp [f, d, cubeColorV, cubeColorSignV, Function.update, hrs]
  have hfs : f s = cubeColorSignV q := by
    simp [f, d, cubeColorV, cubeColorSignV, Function.update]
  have hS :
      (∏ i ∈ S, f i) =
        cubeChar ((S.erase r).erase s) (cubeColorV c) *
          cubeColorSignV p * cubeColorSignV q := by
    calc
      (∏ i ∈ S, f i)
          = (∏ i ∈ S.erase r, f i) * f r := by
              rw [Finset.prod_erase_mul S f hr]
      _ = ((∏ i ∈ (S.erase r).erase s, f i) * f s) * f r := by
              rw [Finset.prod_erase_mul (S.erase r) f hs_erased]
      _ = cubeChar ((S.erase r).erase s) (cubeColorV c) *
            cubeColorSignV p * cubeColorSignV q := by
              rw [hprod_rest, hfr, hfs]
              ring
  unfold cubeChar
  exact hS

/-- The average character multiplier in the square test is nonnegative. -/
theorem cubeColorMultiplierAverage_nonneg {m : ℕ} (S : Finset (Fin m)) :
    0 ≤ cubeColorMultiplierAverage S := by
  unfold cubeColorMultiplierAverage
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro c _hc
    exact sq_nonneg
      ((1 - cubeChar S (cubeColorU c)) * (1 - cubeChar S (cubeColorV c)))
  · exact Nat.cast_nonneg _

/-- The finite color-counting lower bound behind `lem:cube-square`.

For characters of weight at least two, the square-test multiplier has average
at least `32/9`.  This is the only remaining counting calculation in the
cube-square proof. -/
theorem cubeColorMultiplierAverage_lower_of_two_le_card {m : ℕ}
    {S : Finset (Fin m)} (hS : 2 ≤ S.card) :
    (32 / 9 : ℝ) ≤ cubeColorMultiplierAverage S := by
  have hS' : 1 < S.card := by omega
  rcases Finset.one_lt_card.mp hS' with ⟨r, hr, s, hs, hrs⟩
  let F : CubeDirectionColor m → ℝ :=
    fun c =>
      ((1 - cubeChar S (cubeColorU c)) *
        (1 - cubeChar S (cubeColorV c))) ^ (2 : ℕ)
  have hinner (c : CubeDirectionColor m) :
      (32 : ℝ) ≤
        ∑ p : Fin 3,
          ∑ q : Fin 3,
            F (Function.update (Function.update c r p) s q) := by
    let A : ℝ := cubeChar ((S.erase r).erase s) (cubeColorU c)
    let B : ℝ := cubeChar ((S.erase r).erase s) (cubeColorV c)
    have hA : A = 1 ∨ A = -1 := by
      apply sq_eq_one_iff.mp
      simpa [A, pow_two] using
        cubeChar_mul_self ((S.erase r).erase s) (cubeColorU c)
    have hB : B = 1 ∨ B = -1 := by
      apply sq_eq_one_iff.mp
      simpa [B, pow_two] using
        cubeChar_mul_self ((S.erase r).erase s) (cubeColorV c)
    have hlocal := cubeColor_twoCoord_sum_lower (A := A) (B := B) hA hB
    simpa [F, A, B, cubeChar_cubeColorU_update_update S hr hs hrs c,
      cubeChar_cubeColorV_update_update S hr hs hrs c, mul_comm, mul_left_comm,
      mul_assoc] using hlocal
  have htriple_lower :
      (Fintype.card (CubeDirectionColor m) : ℝ) * 32 ≤
        ∑ c : CubeDirectionColor m,
          ∑ p : Fin 3,
            ∑ q : Fin 3,
              F (Function.update (Function.update c r p) s q) := by
    calc
      (Fintype.card (CubeDirectionColor m) : ℝ) * 32
          = ∑ _c : CubeDirectionColor m, (32 : ℝ) := by
              simp [Finset.card_univ]
      _ ≤
        ∑ c : CubeDirectionColor m,
          ∑ p : Fin 3,
            ∑ q : Fin 3,
              F (Function.update (Function.update c r p) s q) := by
          apply Finset.sum_le_sum
          intro c _
          exact hinner c
  rw [cubeColor_sum_update_update r s hrs F] at htriple_lower
  have hcard_pos : (0 : ℝ) < (Fintype.card (CubeDirectionColor m) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (CubeDirectionColor m))
  unfold cubeColorMultiplierAverage
  change (32 / 9 : ℝ) ≤ (∑ c : CubeDirectionColor m, F c) /
    (Fintype.card (CubeDirectionColor m) : ℝ)
  field_simp [hcard_pos.ne']
  nlinarith

/-- Lemma 4.1, `lem:cube-square`: square tests detect high Fourier weight. -/
theorem S04_Lem4_01_CubeSquare (m : ℕ) (g : Cube m → ℝ) :
    (32 / 9 : ℝ) * cubeHighDegreeEnergy g ≤ cubeSquareEnergy g := by
  rw [cubeSquareEnergy_spectral_formula]
  unfold cubeHighDegreeEnergy
  rw [Finset.mul_sum]
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro S _hS
  by_cases hdeg : 2 ≤ S.card
  · have hcoeff_nonneg : 0 ≤ (cubeFourierCoeff g S) ^ (2 : ℕ) :=
      sq_nonneg _
    have hmul :=
      mul_le_mul_of_nonneg_left
        (cubeColorMultiplierAverage_lower_of_two_le_card (m := m) (S := S) hdeg)
        hcoeff_nonneg
    simpa [hdeg, mul_comm, mul_left_comm, mul_assoc] using hmul
  · have hnonneg :
        0 ≤ (cubeFourierCoeff g S) ^ (2 : ℕ) * cubeColorMultiplierAverage S :=
      mul_nonneg (sq_nonneg _) (cubeColorMultiplierAverage_nonneg S)
    simpa [hdeg] using hnonneg

end DictatorshipTesting
