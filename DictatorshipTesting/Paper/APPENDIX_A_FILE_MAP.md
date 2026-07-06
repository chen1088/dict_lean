# Appendix A File Map

Source checked: `../dictatorship_testing_soda27_latest.tex`.

Appendix A statement count: 5.
Appendix A Lean-facing file count: 5.

| Status | Appendix stmt | Title | Lean file | What it supplies | Source/citation target | Notes |
| --- | --- | --- | --- | --- | --- | --- |
| external: cited representation-theory input | A.1 | Young orthogonal realization | `AppA_ThmA_01_YoungOrthogonalRealization.lean` | Classical Specht/Young orthogonal realization; Section 5 separately proves the coordinate Coxeter model | Classical Young orthogonal/Specht module theory | Appendix A.1 boundary; no import from internal Section 5 theorem files. |
| external: cited representation-theory input | A.2 | Jucys--Murphy content spectrum | `AppA_ThmA_02_JucysMurphyContentSpectrum.lean` | Classical group-algebra Jucys--Murphy content spectrum; Section 5 separately proves diagonal content eigenspaces | Standard Jucys--Murphy content-spectrum theorem | Appendix A.2 boundary; no import from internal Section 5 theorem files. |
| external: cited representation-theory input | A.3 | Regular Young-block decomposition | `AppA_ThmA_03_RegularYoungBlockDecomposition.lean` | `AppA_ThmA_03_YoungBlockDecompositionInput`, `AppA_ThmA_03_U1YoungBlockIdentificationInput`, and block-energy consequences | Regular representation/Specht decomposition and Schur orthogonality | Appendix A.3 boundary. |
| external: cited representation-theory input | A.4 | Degree-one Young-block identification | `AppA_LemA_04_DegreeOneYoungBlockIdentification.lean` | `U_1` Young-block identification interface and non-`U_1` block set wrappers | Degree-one permutation representation decomposition | Appendix A.4 boundary. |
| external: cited representation-theory input | A.5 | Connectedness of standard tableaux | `AppA_LemA_05_StandardTableauxSwapConnectedness.lean` | External connectedness theorem for adjacent swaps of standard tableaux of a fixed shape | Standard tableaux graph connectedness | Appendix A.5 boundary. |

The Appendix A files intentionally do not introduce new axioms.  They either
document an external input boundary or expose neutral auxiliary interface
definitions already used by the Section 5 scaffold.  Appendix A files should
not import internal `S05_*` theorem files.
