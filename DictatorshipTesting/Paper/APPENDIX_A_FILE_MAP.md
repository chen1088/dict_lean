# Appendix A File Map

Source checked: `../dictatorship_testing_soda27_latest.tex`.

Appendix A statement count: 5.
Appendix A Lean-facing file count: 5.

| Status | Paper stmt | Environment | Paper title | Lean file | Main wrappers | Notes |
| --- | --- | --- | --- | --- | --- | --- |
| external: Young orthogonal/Specht module theory | A.1 | theorem | Young orthogonal realization | `AppA_ThmA_01_YoungOrthogonalRealization.lean` | Documentation boundary file | Classical Specht/Young orthogonal realization; Section 5 separately proves the coordinate Coxeter model. |
| external: Jucys--Murphy content-spectrum theorem | A.2 | theorem | Jucys--Murphy content spectrum | `AppA_ThmA_02_JucysMurphyContentSpectrum.lean` | Documentation boundary file | Classical group-algebra Jucys--Murphy content spectrum; Section 5 separately proves diagonal content eigenspaces. |
| external: regular representation/Specht decomposition and Schur orthogonality | A.3 | theorem | Regular Young-block decomposition | `AppA_ThmA_03_RegularYoungBlockDecomposition.lean` | `AppA_ThmA_03_YoungBlockDecompositionInput`, `AppA_ThmA_03_U1YoungBlockIdentificationInput` | Supplies the Young-block energy decomposition and the `U_1` block identification interface. |
| external: degree-one permutation representation decomposition | A.4 | lemma | Degree-one Young-block identification | `AppA_LemA_04_DegreeOneYoungBlockIdentification.lean` | `AppA_LemA_04_U1YoungBlockIdentification`, `AppA_LemA_04_l2DistSqToU1_eq_nonU1_sum` | Identifies the non-`U_1` block set used by the spectral model. |
| external: standard tableaux swap connectedness | A.5 | lemma | Connectedness of standard tableaux | `AppA_LemA_05_StandardTableauxSwapConnectedness.lean` | Documentation boundary file | External connectedness fact for adjacent swaps of standard tableaux of a fixed shape. |

The Appendix A files intentionally do not introduce new axioms.  They either
document an external input boundary or expose neutral auxiliary interface
definitions already used by the Section 5 scaffold.  Appendix A files should
not import internal `S05_*` theorem files.
