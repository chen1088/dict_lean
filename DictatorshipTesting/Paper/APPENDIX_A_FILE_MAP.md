# Appendix A File Map

Source checked: `../dictatorship_testing_soda27_latest.tex`.

Appendix A statement count: 4.
Appendix A Lean-facing file count: 4.

| Status | Paper stmt | Environment | Paper title | Lean file | Main wrappers | Notes |
| --- | --- | --- | --- | --- | --- | --- |
| external: ingredient for Lemma 5.18 spectral model | A.1 | theorem | Young orthogonal realization | `AppA_ThmA_01_YoungOrthogonalRealization.lean` | `AppA_ThmA_01_youngOrthogonalRealization` | Classical Specht/Young orthogonal realization; Section 5 separately proves the coordinate Coxeter model. |
| external: ingredient for Lemma 5.18 spectral model | A.2 | theorem | Jucys--Murphy content spectrum | `AppA_ThmA_02_JucysMurphyContentSpectrum.lean` | `AppA_ThmA_02_jucysMurphyContentSpectrum` | Classical group-algebra Jucys--Murphy content spectrum; Section 5 separately proves diagonal content eigenspaces.  The Lean file imports only neutral height definition files for `hEvenTableau`/`hOddTableau`, not the certificate proof files. |
| external: degree-one permutation representation decomposition | A.3 | lemma | Degree-one Young-block identification | `AppA_LemA_03_DegreeOneYoungBlockIdentification.lean` | `AppA_LemA_03_degreeOneYoungBlockIdentification`, `AppA_LemA_03_l2DistSqToU1_eq_nonU1_sum` | The marker axiom records the external representation input; the remaining wrappers expose the Lean `U_1` block-identification interface used by the spectral model. |
| external: standard-tableaux connectedness | A.4 | lemma | Connectedness of standard tableaux | `AppA_LemA_04_StandardTableauxSwapConnectedness.lean` | `AppA_LemA_04_standardTableauxSwapConnectedness` | External connectedness fact for adjacent swaps of standard tableaux of a fixed shape. This statement is connectedness only. |

Appendix A now has explicit Lean axiom declarations for each external paper
ingredient A.1, A.2, A.3, and A.4.
The matching-average bridge is now isolated as the Section 5 input
`S05_matchingAverageScalarity_from_young_model_input`,
outside Appendix A.  The regular Young-block decomposition has moved to
Section 5 as Lemma 5.18.  Its theorem wrappers
`spectralBlockModelInputWithDim_even_from_appendixA` and
`spectralBlockModelInputWithDim_odd_from_appendixA` are the names used
downstream by Theorem 4.8.
