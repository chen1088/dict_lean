import DictatorshipTesting.Paper.Aux_BooleanU1StructuralInput

/-!
# Theorem 2.1: Boolean degree-one functions on `Sₙ`

This is the paper's structural input `thm:boolean-u1`.
-/

namespace DictatorshipTesting

/-- Theorem 2.1, `thm:boolean-u1`: Boolean functions in `U₁` are exactly dictators. -/
theorem Thm2_1_BooleanU1 (n : ℕ) (f : BoolFn (Fin n)) :
    boolFnToReal f ∈ U1 (Fin n) ↔ IsDictator f := by
  exact booleanU1_iff_dictator_input n f

end DictatorshipTesting
