import DictatorshipTesting.Paper.Defs.S05_IntDef_ZEven
import DictatorshipTesting.Paper.S05_Int_TableauDimension

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S05_Def5_25_TableauOddHeight`
- `DictatorshipTesting.Paper.S05_Lem5_19_RegularYoungBlockDecomposition`
- `DictatorshipTesting.Paper.S05_Lem5_25_EvenCertificate`
-/

/-!
Definition file for `hEvenTableau`.

This neutral height function is used both by the finite certificate proof and by
the Appendix A spectral-model interface.
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
