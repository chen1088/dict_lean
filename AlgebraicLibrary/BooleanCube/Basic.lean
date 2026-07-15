import Mathlib.Data.Real.Basic

/-!
# Boolean cubes

Basic operations on a Boolean cube indexed by an arbitrary finite coordinate
type.  `Fin n` is only one possible choice of coordinates.
-/

noncomputable section

namespace AlgebraicLibrary

/-- The Boolean cube indexed by `ι`. -/
abbrev BooleanCube (ι : Type*) := ι → Bool

/-- Short compatibility name for `BooleanCube`. -/
abbrev Cube (ι : Type*) := BooleanCube ι

/-- A Boolean cube with the paper-common finite coordinate type `Fin m`. -/
abbrev FinCube (m : Nat) := Cube (Fin m)

/-- Map a Boolean value to its `{0,1}` real indicator. -/
def boolToReal (b : Bool) : ℝ :=
  if b then 1 else 0

/-- Coordinatewise xor on a Boolean cube. -/
def cubeXor {ι : Type*} (x y : Cube ι) : Cube ι :=
  fun i => x i ^^ y i

/-- The zero point of a Boolean cube. -/
def cubeZero (ι : Type*) : Cube ι :=
  fun _ => false

@[simp] theorem cubeZero_apply (ι : Type*) (i : ι) : cubeZero ι i = false := rfl

/-- The zero point of a `Fin`-indexed Boolean cube. -/
abbrev finCubeZero (m : Nat) : FinCube m := cubeZero (Fin m)

/-- Flip one coordinate of a Boolean-cube point. -/
def cubeFlip {ι : Type*} [DecidableEq ι] (i : ι) (x : Cube ι) : Cube ι :=
  Function.update x i (!(x i))

/-- Two cube directions have disjoint supports. -/
def CubeDirectionsDisjoint {ι : Type*} (u v : Cube ι) : Prop :=
  ∀ i, u i = true → v i = false

/-- A Boolean-cube function is constant. -/
def IsCubeConstant {ι : Type*} (g : Cube ι → Bool) : Prop :=
  ∀ x y, g x = g y

/-- A Boolean-cube function depends only on coordinate `i`. -/
def IsCubeJuntaAt {ι : Type*} (g : Cube ι → Bool) (i : ι) : Prop :=
  ∀ x y, x i = y i → g x = g y

/-- A Boolean-cube function depends on at most one coordinate. -/
def IsCubeOneJunta {ι : Type*} (g : Cube ι → Bool) : Prop :=
  IsCubeConstant g ∨ ∃ i, IsCubeJuntaAt g i

/-- Xor with the zero cube point on the right. -/
@[simp] theorem cubeXor_zero {ι : Type*} (x : Cube ι) :
    cubeXor x (cubeZero ι) = x := by
  ext i
  simp [cubeXor, cubeZero]

/-- Xor with the zero cube point on the left. -/
@[simp] theorem cubeZero_xor {ι : Type*} (x : Cube ι) :
    cubeXor (cubeZero ι) x = x := by
  ext i
  simp [cubeXor, cubeZero]

/-- Coordinatewise xor is associative. -/
theorem cubeXor_assoc {ι : Type*} (x y z : Cube ι) :
    cubeXor (cubeXor x y) z = cubeXor x (cubeXor y z) := by
  ext i
  simp [cubeXor]

/-- Coordinatewise xor is commutative. -/
theorem cubeXor_comm {ι : Type*} (x y : Cube ι) :
    cubeXor x y = cubeXor y x := by
  ext i
  simp [cubeXor, Bool.xor_comm]

/-- Xoring by the same point twice on the left is the identity. -/
@[simp] theorem cubeXor_self_left {ι : Type*} (z x : Cube ι) :
    cubeXor z (cubeXor z x) = x := by
  ext i
  by_cases hz : z i <;> simp [cubeXor, hz]

/-- Xoring by the same point twice on the right is the identity. -/
@[simp] theorem cubeXor_self_right {ι : Type*} (x z : Cube ι) :
    cubeXor (cubeXor x z) z = x := by
  ext i
  by_cases hz : z i <;> simp [cubeXor, hz]

/-- Translation by a fixed cube point as an equivalence. -/
def cubeXorEquiv {ι : Type*} (z : Cube ι) : Cube ι ≃ Cube ι where
  toFun x := cubeXor z x
  invFun x := cubeXor z x
  left_inv := cubeXor_self_left z
  right_inv := cubeXor_self_left z

/-- Flipping the same Boolean-cube coordinate twice is the identity. -/
@[simp] theorem cubeFlip_involutive {ι : Type*} [DecidableEq ι]
    (i : ι) (x : Cube ι) : cubeFlip i (cubeFlip i x) = x := by
  ext j
  by_cases hji : j = i <;> simp [cubeFlip, hji]

end AlgebraicLibrary
