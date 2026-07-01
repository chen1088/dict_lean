import DictatorshipTesting.Paper.Aux_CubeCharXor

/-!
# Square differences of cube characters
-/

namespace DictatorshipTesting

/-- The square difference of one cube character factors as in the paper. -/
theorem cubeDelta_cubeChar {m : ℕ} (S : Finset (Fin m))
    (x u v : Cube m) :
    cubeDelta (cubeChar S) x u v =
      cubeChar S x * (1 - cubeChar S u) * (1 - cubeChar S v) := by
  unfold cubeDelta
  rw [cubeChar_cubeXor S x u, cubeChar_cubeXor S x v]
  have hlast :
      cubeChar S (cubeXor (cubeXor x u) v) =
        cubeChar S x * cubeChar S u * cubeChar S v := by
    rw [cubeChar_cubeXor S (cubeXor x u) v, cubeChar_cubeXor S x u]
  rw [hlast]
  ring

end DictatorshipTesting
