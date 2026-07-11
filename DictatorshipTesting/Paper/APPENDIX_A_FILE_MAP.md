# Appendix A File Map

Source checked: `../dictatorship_testing_soda27_latest.tex`.

Appendix A statement count: 3.
Appendix A Lean-facing file count: 3.

| Status | Paper stmt | Environment | Paper title | Lean file | Main wrappers | Notes |
| --- | --- | --- | --- | --- | --- | --- |
| external axiom still uses old numerical shadow; faithful action interface defined | A.1 | theorem | Young orthogonal realization | `AppA_ThmA_01_YoungOrthogonalRealization.lean` | `AppA_ThmA_01_YoungOrthogonalActionStatement`, `AppA_ThmA_01_youngOrthogonalRealization` | `YoungOrthogonalActionData` records the representation and identifies each literal adjacent swap `(a,a+1)` with the concrete Young operator.  Lemma 5.19 proves the concrete matrix-coefficient theory parametrically from this faithful data.  The existing axiom keeps its old block-energy type until completeness and the active adapter are rebuilt. |
| external axiom still uses old numerical shadow; faithful content interface defined | A.2 | theorem | Jucys--Murphy content spectrum | `AppA_ThmA_02_JucysMurphyContentSpectrum.lean` | `AppA_ThmA_02_JucysMurphyContentActionStatement`, `AppA_ThmA_02_jucysMurphyContentSpectrum` | `JucysMurphyContentActionData` ties the actual `J_k` coefficient element to the same A.1 action and the diagonal content operator.  Lemmas 5.11 and 5.13 prove the intended even/odd matching bases and fixed traces; Lemma 5.19 uses content spectra to prove cross-shape orthogonality.  The existing axiom keeps its old trace/scalar type until the faithful global adapter is complete. |
| external: degree-one permutation representation decomposition | A.3 | lemma | Degree-one Young-block identification | `AppA_LemA_03_DegreeOneYoungBlockIdentification.lean` | `AppA_LemA_03_degreeOneYoungBlockIdentification`, `AppA_LemA_03_l2DistSqToU1_eq_nonU1_sum` | The marker axiom records the external representation input; the remaining wrappers expose the Lean `U_1` block-identification interface used by the spectral model. |

Appendix A has explicit Lean axiom declarations for the remaining external
paper ingredients A.1, A.2, and A.3.  Standard-tableau connectedness is now
internal Lemma 5.3 and is not an Appendix statement.
Faithful operator-level statement definitions for A.1 and A.2 are present, but
the two existing axiom declarations have not yet been changed from their old
numerical-shadow types; doing so before the regular decomposition and concrete
global adapters exist would break the active Theorem 4.8 route.  The concrete
matrix-coefficient family is orthogonal and linearly independent, and its block
components and Parseval identity are constructed from the explicit cardinality
equality.  The first missing theorem is the RSK/sum-of-squares equality
`sum lambda, tableauDimNat lambda ^ 2 = (n + 1)!`; the faithful A.3 `U_1`
adapter remains after it.
The matching-average bridge is now isolated as the Section 5 input
`S05_matchingAverageScalarity_from_young_model_input`,
outside Appendix A.  The regular Young-block decomposition has moved to
Section 5 as Lemma 5.19.  Its theorem wrappers
`spectralBlockModelInputWithDim_even_from_appendixA` and
`spectralBlockModelInputWithDim_odd_from_appendixA` are the names used
downstream by Theorem 4.8.
