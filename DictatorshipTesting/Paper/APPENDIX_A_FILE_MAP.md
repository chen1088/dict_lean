# Appendix A File Map

Source checked: `../dictatorship_testing_soda27_latest.tex`.

Appendix A statement count: 5.
Appendix A Lean-facing file count: 5.

| Status | Paper stmt | Environment | Paper title | Lean file | Main wrappers | Notes |
| --- | --- | --- | --- | --- | --- | --- |
| external: ingredient bundled into A.3 spectral model | A.1 | theorem | Young orthogonal realization | `AppA_ThmA_01_YoungOrthogonalRealization.lean` | `AppA_ThmA_01_youngOrthogonalRealization` | Classical Specht/Young orthogonal realization; Section 5 separately proves the coordinate Coxeter model. |
| external: ingredient bundled into A.3 spectral model | A.2 | theorem | Jucys--Murphy content spectrum | `AppA_ThmA_02_JucysMurphyContentSpectrum.lean` | `AppA_ThmA_02_jucysMurphyContentSpectrum` | Classical group-algebra Jucys--Murphy content spectrum; Section 5 separately proves diagonal content eigenspaces. |
| proven internal assembly from external ingredients | A.3 | theorem | Regular Young-block decomposition | `AppA_ThmA_03_RegularYoungBlockDecomposition.lean` | `spectralBlockModelInputWithDim_even_from_appA_inputs`, `spectralBlockModelInputWithDim_odd_from_appA_inputs`, `spectralBlockModelInputWithDim_even_from_appendixA`, `spectralBlockModelInputWithDim_odd_from_appendixA` | A.3 has no standalone axiom: it assembles the explicit A.1/A.2/A.4/A.5 marker inputs into the `SpectralBlockModelInputWithDim` interface consumed downstream. |
| external: degree-one permutation representation decomposition | A.4 | lemma | Degree-one Young-block identification | `AppA_LemA_04_DegreeOneYoungBlockIdentification.lean` | `AppA_LemA_04_degreeOneYoungBlockIdentification`, `AppA_LemA_04_l2DistSqToU1_eq_nonU1_sum` | The marker axiom records the external representation input; the remaining wrappers expose the Lean `U_1` block-identification interface used by the spectral model. |
| external: ingredient bundled into A.3 spectral model | A.5 | lemma | Connectedness of standard tableaux | `AppA_LemA_05_StandardTableauxSwapConnectedness.lean` | `AppA_LemA_05_standardTableauxSwapConnectedness` | External connectedness fact for adjacent swaps of standard tableaux of a fixed shape. |

Appendix A now has explicit Lean axiom declarations for each external paper
ingredient A.1, A.2, A.4, and A.5.  Theorem A.3 is not an additional external
input: `spectralBlockModelInputWithDim_even_from_appA_inputs` and
`spectralBlockModelInputWithDim_odd_from_appA_inputs` are proved assembly
theorems that consume those ingredient markers.  The names used downstream by
Theorem 4.10 are theorem wrappers
`spectralBlockModelInputWithDim_even_from_appendixA` and
`spectralBlockModelInputWithDim_odd_from_appendixA`.
