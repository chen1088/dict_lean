import DictatorshipTesting.Paper.Defs.S02_IntDef_BoolFn
import AlgebraicLibrary.Combinatorics.OrderedMatching.Basic

open AlgebraicLibrary
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S03_IntDef_CubeDirectionColor`
- `DictatorshipTesting.Paper.S03_Lem3_01_DictatorToJunta`
-/


/-!
Definition file for `matchingCubeRestriction`.
-/

noncomputable section

namespace DictatorshipTesting

/-- Restrict a Boolean function on permutations to a matching cube based at `pi`. -/
def matchingCubeRestriction {α : Type*} [DecidableEq α]
    (f : BoolFn α) (M : OrderedMatching α) (π : Perm α) :
    FinCube M.edgeCount → Bool :=
  fun x => f (π * M.tau x)

end DictatorshipTesting
