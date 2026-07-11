# Appendix A File Map

Source checked: `../dictatorship_testing_soda27_latest.tex`.

Appendix A statement count: 3.
Appendix A Lean-facing file count: 3.

| Status | Paper stmt | Environment | Paper title | Lean file | Main wrappers | Notes |
| --- | --- | --- | --- | --- | --- | --- |
| proven internally | A.1 | theorem | Young orthogonal realization | `AppA_ThmA_01_YoungOrthogonalRealization.lean` | `AppA_ThmA_01_YoungOrthogonalActionStatement`, `AppA_ThmA_01_youngOrthogonalRealization` | `S05_Int_AdjacentCoxeterPresentation.lean` proves the complete type-A adjacent-word presentation and constructs `YoungOrthogonalActionData`, identifying each literal adjacent swap `(a,a+1)` with the concrete Young operator. |
| proven internally | A.2 | theorem | Jucys--Murphy content spectrum | `AppA_ThmA_02_JucysMurphyContentSpectrum.lean` | `AppA_ThmA_02_JucysMurphyContentActionStatement`, `AppA_ThmA_02_jucysMurphyContentSpectrum` | `S05_Int_JucysMurphyContentAction.lean` proves the group-algebra recurrence, the tableau content recurrence, and the finite induction for every A.1 action. The former trace payload is unnecessary: matching traces and universal positivity of `tableauDim` are proved internally. |
| proven internally | A.3 | lemma | Degree-one Young-block identification | `AppA_LemA_03_DegreeOneYoungBlockIdentification.lean` | `AppA_LemA_03_degreeOneYoungBlockIdentification`, `AppA_LemA_03_U1_eq_concreteDegreeOneYoungBlockSum`, `AppA_LemA_03_l2DistSqToU1_eq_nonU1_sum` | `S05_Int_DegreeOneYoungBlock.lean` proves `U1 =` the concrete sum of the one-row and standard matrix-coefficient blocks by an explicit permutation-coordinate decomposition. Lemma 5.19 derives the complementary-energy distance identity from this equality, orthogonality, and the defining `sInf`. |

All three Appendix A statements are proved internally.  Standard-tableau
connectedness is internal Lemma 5.3 and is not an Appendix statement.
The A.1 theorem constructs its faithful operator action from the type-A
Coxeter presentation.  A.2 derives its faithful content action from the
Jucys--Murphy and tableau-operator recurrences.  The concrete
matrix-coefficient family is orthogonal and
linearly independent, its block components and Parseval identity are
unconditional, and the Young-tableau sum-of-squares equality is internal.
Faithful A.3 and its connection to the active numerical model are internally
proved.
The matching-average bridge is proved internally in Section 5 as part of Lemma
5.19.  The regular Young-block decomposition theorem wrappers
`spectralBlockModelInputWithDim_even_from_appendixA` and
`spectralBlockModelInputWithDim_odd_from_appendixA` are the names used
downstream by Theorem 4.8.
