import DictatorshipTesting.Paper.AppA_ThmA_01_YoungOrthogonalRealization
import DictatorshipTesting.Paper.Defs.AppA_DefA_02_JucysMurphyContentActionData
import DictatorshipTesting.Paper.S05_Int_TableauDimension
import DictatorshipTesting.Paper.Defs.S05_Def5_24_TableauEvenHeight
import DictatorshipTesting.Paper.Defs.S05_Def5_25_TableauOddHeight

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_19_RegularYoungBlockDecomposition`
-/

/-!
Paper statement: Theorem A.2 (`thm:app-jucys-murphy-content`)
Title in paper: Jucys--Murphy content spectrum.

Status: external: ingredient bundled into Lemma 5.20.  This file is kept
separate from the internal Section 5 diagonal-content eigenspace proof: the
classical group-algebra Jucys--Murphy content-spectrum theorem is consumed in
Lean through the Lemma 5.19 spectral-block assembly theorem in
`S05_Lem5_19_RegularYoungBlockDecomposition`.
-/


noncomputable section

namespace DictatorshipTesting

/-- Faithful operator-level statement of Theorem A.2: for each A.1 action, the
actual Jucys--Murphy coefficient elements act as the explicit diagonal content
operators. -/
def AppA_ThmA_02_JucysMurphyContentActionStatement : Prop :=
  ∀ {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam),
    Nonempty (JucysMurphyContentActionData action)

/-- Trace/scalar data supplied by the Jucys--Murphy content-spectrum
calculation, parameterized by the block dimension and height functions. -/
structure AppA_TraceScalarDataWithDim {n : Nat}
    (dim height : YoungDiagram n -> ℝ)
    {F : Perm (Fin n) -> ℝ}
    (energy : AppA_YoungBlockEnergyData F) where
  theta : YoungDiagram n -> ℝ
  trace_value : TraceScalarValueInputWithDim dim height theta

/-- Trace/scalar payload of A.2 used by the active matching calculation. -/
def AppA_ThmA_02_TraceScalarStatement : Prop :=
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

/-- Faithful A.2 content action together with its trace/scalar consequence. -/
def AppA_ThmA_02_JucysMurphyContentSpectrumStatement : Prop :=
  AppA_ThmA_02_JucysMurphyContentActionStatement ∧
    AppA_ThmA_02_TraceScalarStatement

/-- External A.2 input in faithful content-action form, bundled with the trace
payload used by the matching spectral calculation. -/
axiom AppA_ThmA_02_jucysMurphyContentSpectrum :
    AppA_ThmA_02_JucysMurphyContentSpectrumStatement

end DictatorshipTesting
