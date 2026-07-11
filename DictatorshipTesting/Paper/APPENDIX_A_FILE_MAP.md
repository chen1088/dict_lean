# Appendix A File Map

Source checked: `../dictatorship_testing_soda27_latest.tex`.

Appendix A statement count: 3.
Appendix A Lean-facing file count: 3.

| Status | Paper stmt | Environment | Paper title | Lean file | Main wrappers | Notes |
| --- | --- | --- | --- | --- | --- | --- |
| external: faithful Young action | A.1 | theorem | Young orthogonal realization | `AppA_ThmA_01_YoungOrthogonalRealization.lean` | `AppA_ThmA_01_YoungOrthogonalActionStatement`, `AppA_ThmA_01_youngOrthogonalRealization` | The axiom has the faithful operator-level type. `YoungOrthogonalActionData` records the representation and identifies each literal adjacent swap `(a,a+1)` with the concrete Young operator. |
| external: faithful content action and trace payload | A.2 | theorem | Jucys--Murphy content spectrum | `AppA_ThmA_02_JucysMurphyContentSpectrum.lean` | `AppA_ThmA_02_JucysMurphyContentActionStatement`, `AppA_ThmA_02_TraceScalarStatement`, `AppA_ThmA_02_jucysMurphyContentSpectrum` | The axiom supplies `JucysMurphyContentActionData` for each A.1 action together with the even/odd trace-scalar payload used by the active matching calculation. |
| external: faithful concrete subspace equality | A.3 | lemma | Degree-one Young-block identification | `AppA_LemA_03_DegreeOneYoungBlockIdentification.lean` | `AppA_LemA_03_degreeOneYoungBlockIdentification`, `AppA_LemA_03_U1_eq_concreteDegreeOneYoungBlockSum`, `AppA_LemA_03_l2DistSqToU1_eq_nonU1_sum` | The axiom states `U1 =` the concrete sum of the one-row and standard matrix-coefficient blocks. Lemma 5.19 derives the complementary-energy distance identity internally from this equality, orthogonality, and the defining `sInf`. |

Appendix A has explicit Lean axiom declarations for the remaining external
paper ingredients A.1, A.2, and A.3.  Standard-tableau connectedness is now
internal Lemma 5.3 and is not an Appendix statement.
The A.1 and A.3 axiom declarations now have their faithful operator/subspace
types.  A.2 bundles its faithful content action with the trace/scalar payload
used downstream.  The concrete matrix-coefficient family is orthogonal and
linearly independent, its block components and Parseval identity are
unconditional, and the Young-tableau sum-of-squares equality is internal.
Faithful A.3 is connected to the active numerical model by the internally
proved complementary-energy distance theorem.
The matching-average bridge is proved internally in Section 5 as part of Lemma
5.19.  The regular Young-block decomposition theorem wrappers
`spectralBlockModelInputWithDim_even_from_appendixA` and
`spectralBlockModelInputWithDim_odd_from_appendixA` are the names used
downstream by Theorem 4.8.
