# Appendix A File Map

Source checked: `../dictatorship_testing_soda27_latest.tex`.

Appendix A statement count: 5.
Appendix A Lean-facing file count: 5.

| Appendix stmt | Title | Lean file | What it supplies | Lean status | Source/citation target |
| --- | --- | --- | --- | --- | --- |
| A.1 | Young orthogonal realization | `AppA_ThmA_01_YoungOrthogonalRealization.lean` | Documents the external identification of the proved coordinate Coxeter model with the classical Specht/Young orthogonal realization | external: Appendix A.1 Young orthogonal/Specht realization | Classical Young orthogonal/Specht module theory |
| A.2 | Jucys--Murphy content spectrum | `AppA_ThmA_02_JucysMurphyContentSpectrum.lean` | Documents the external identification of diagonal content operators with group-algebra Jucys--Murphy elements | external: Appendix A.2 Jucys--Murphy theorem | Standard Jucys--Murphy content-spectrum theorem |
| A.3 | Regular Young-block decomposition | `AppA_ThmA_03_RegularYoungBlockDecomposition.lean` | Exposes `AppA_ThmA_03_YoungBlockDecompositionInput`, `AppA_ThmA_03_U1YoungBlockIdentificationInput`, and block-energy consequences | external: Appendix A.3 regular Young-block decomposition | Regular representation/Specht decomposition and Schur orthogonality |
| A.4 | Degree-one Young-block identification | `AppA_LemA_04_DegreeOneYoungBlockIdentification.lean` | Exposes the `U_1` Young-block identification interface and non-`U_1` block set wrappers | external: Appendix A.4 degree-one Young-block identification | Degree-one permutation representation decomposition |
| A.5 | Connectedness of standard tableaux | `AppA_LemA_05_StandardTableauxSwapConnectedness.lean` | Documents the external connectedness theorem for adjacent swaps of standard tableaux of a fixed shape | external: Appendix A.5 standard-tableau swap connectedness | Standard tableaux graph connectedness |

The Appendix A files intentionally do not introduce new axioms.  They either
document an external input boundary or expose existing interface definitions
already used by the Section 5 scaffold.
