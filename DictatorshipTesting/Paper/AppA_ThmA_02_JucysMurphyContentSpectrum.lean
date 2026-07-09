import DictatorshipTesting.Paper.AppA_ThmA_01_YoungOrthogonalRealization
import DictatorshipTesting.Paper.S05_Int_TableauDimension
import DictatorshipTesting.Paper.Defs.S05_Def5_24_TableauEvenHeight
import DictatorshipTesting.Paper.Defs.S05_Def5_25_TableauOddHeight

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.AppA_LemA_04_StandardTableauxSwapConnectedness`
- `DictatorshipTesting.Paper.S05_Lem5_18_RegularYoungBlockDecomposition`
-/

/-!
Paper statement: Theorem A.2 (`thm:app-jucys-murphy-content`)
Title in paper: Jucys--Murphy content spectrum.

Status: external: ingredient bundled into Lemma 5.18.  This file is kept
separate from the internal Section 5 diagonal-content eigenspace proof: the
classical group-algebra Jucys--Murphy content-spectrum theorem is consumed in
Lean through the Lemma 5.18 spectral-block assembly theorem in
`S05_Lem5_18_RegularYoungBlockDecomposition`.
-/


noncomputable section

namespace DictatorshipTesting

/-- Trace/scalar data supplied by the Jucys--Murphy content-spectrum
calculation, parameterized by the block dimension and height functions. -/
structure AppA_TraceScalarDataWithDim {n : Nat}
    (dim height : YoungDiagram n -> ℝ)
    {F : Perm (Fin n) -> ℝ}
    (energy : AppA_YoungBlockEnergyData F) where
  theta : YoungDiagram n -> ℝ
  trace_value : TraceScalarValueInputWithDim dim height theta

/-- Theorem A.2 interface: the content-spectrum calculation supplies the
trace/scalar values needed by the even and odd tableau-count spectral models. -/
def AppA_ThmA_02_JucysMurphyContentSpectrumStatement : Prop :=
  (∀ (m : Nat) (_hm : 2 <= m)
      {F : Perm (Fin (2 * m)) -> ℝ}
      (energy : AppA_YoungBlockEnergyData F),
      Nonempty
        (AppA_TraceScalarDataWithDim
          (fun lam : YoungDiagram (2 * m) => tableauDim lam)
          (fun lam : YoungDiagram (2 * m) => hEvenTableau m lam)
          energy)) ∧
    (∀ (m : Nat) (_hm : 2 <= m)
      {F : Perm (Fin (2 * m + 1)) -> ℝ}
      (energy : AppA_YoungBlockEnergyData F),
      Nonempty
        (AppA_TraceScalarDataWithDim
          (fun lam : YoungDiagram (2 * m + 1) => tableauDim lam)
          (fun lam : YoungDiagram (2 * m + 1) => hOddTableau m lam)
          energy))

/-- External input Theorem A.2: Jucys--Murphy content spectrum. -/
axiom AppA_ThmA_02_jucysMurphyContentSpectrum :
    AppA_ThmA_02_JucysMurphyContentSpectrumStatement

end DictatorshipTesting
