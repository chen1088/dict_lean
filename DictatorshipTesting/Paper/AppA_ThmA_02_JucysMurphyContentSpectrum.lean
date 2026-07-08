/-!
Paper statement: Theorem A.2 (`thm:app-jucys-murphy-content`)
Title in paper: Jucys--Murphy content spectrum.

Status: external: ingredient bundled into Theorem A.3.  This file is kept
separate from the internal Section 5 diagonal-content eigenspace proof: the
classical group-algebra Jucys--Murphy content-spectrum theorem is consumed in
Lean through the packaged spectral-block model axioms in
`AppA_ThmA_03_RegularYoungBlockDecomposition`.
-/

noncomputable section

namespace DictatorshipTesting

/-- Marker proposition for the not-yet-formalized Theorem A.2.  It stands for
the classical Jucys--Murphy content-spectrum theorem used by the packaged
spectral-block model input in Theorem A.3. -/
inductive AppA_ThmA_02_JucysMurphyContentSpectrumStatement : Prop

/-- External input Theorem A.2: Jucys--Murphy content spectrum. -/
axiom AppA_ThmA_02_jucysMurphyContentSpectrum :
    AppA_ThmA_02_JucysMurphyContentSpectrumStatement

end DictatorshipTesting
