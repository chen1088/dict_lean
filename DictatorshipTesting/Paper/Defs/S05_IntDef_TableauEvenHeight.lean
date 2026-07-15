import DictatorshipTesting.Paper.Defs.S05_IntDef_ZEven
import AlgebraicLibrary.Young.TableauDimension

open AlgebraicLibrary

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S05_IntDef_TableauOddHeight`
- `DictatorshipTesting.Paper.S05_Lem5_19_EvenCertificate`
- `DictatorshipTesting.Paper.S05_Prop5_16_AveragedRejectionOnYoungBlocks`
-/
/-!
Definition file for `hEvenTableau`.

This neutral height function is used both by the finite certificate proof and by
the Section 5 spectral-model interface.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Number of high-weight entries in the even matching-branching multiset,
using actual tableau dimensions in the vertical contribution. -/
noncomputable def hEvenTableau : (m : Nat) -> YoungDiagram (2 * m) -> Real
  | 0, _ => 0
  | m + 1, lam =>
      (horizontalTwoStripChildrenEven (m + 1) lam).sum
          (fun mu => hEvenTableau m mu) +
        (verticalTwoStripChildrenEven (m + 1) lam).sum
          (fun mu => tableauDim mu - zEven m mu)

end DictatorshipTesting
