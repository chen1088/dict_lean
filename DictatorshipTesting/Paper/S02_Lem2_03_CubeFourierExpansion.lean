import AlgebraicLibrary.BooleanCube.Fourier

open AlgebraicLibrary

/-! Paper-facing compatibility statements for Lemma 2.3 Fourier inversion. -/

namespace DictatorshipTesting

theorem S02_Lem2_03_cubeFourier_expansion (m : ℕ) :
    ∀ g : FinCube m → ℝ, ∀ x : FinCube m,
      g x = ∑ S : Finset (Fin m), cubeFourierCoeff g S * cubeChar S x := by
  intro g x
  exact AlgebraicLibrary.cubeFourier_expansion g x

end DictatorshipTesting
