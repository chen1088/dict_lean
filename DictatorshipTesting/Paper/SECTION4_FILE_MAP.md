# Section 4 File Map

Source checked: `../dictatorship_testing_soda27_latest.tex`.

Counting rule: theorem-like numbered environments only (`definition`, `lemma`,
`proposition`, `theorem`, `corollary`). Remarks, examples, equations, proofs,
and later-section statements are not represented here.

Section 4 statement count: 13.

| Status | Paper stmt | Environment | Paper title | Lean file | Main wrappers | Notes |
| --- | --- | --- | --- | --- | --- | --- |
| proven | 4.1 | lemma | Square test detects Fourier weight at least two | `S04_Lem4_01_CubeSquare.lean` | `L4_1_CubeSquare` | Boolean-cube square-test Fourier identity. |
| definition/interface | 4.2 | definition | Local degree-one space | `Defs.lean` | `IsMatchingLocalDegreeOne`, `matchingLocalHighDegreeEnergy` | Matching-cube local degree-one vocabulary. |
| definition/interface | 4.3 | definition | Matching-local truncation | `Defs.lean` | `matchingLocalProjection`, `matchingLocalProjectionError` | Local projection and error vocabulary. |
| proven | 4.4 | lemma | The definition of `P_M` is independent of representatives | `S04_Lem4_04_PMIndependentOfRepresentatives.lean` | `L4_4_PMIndependentOfRepresentatives` | Representative-change invariance of the local truncation. |
| proven | 4.5 | lemma | `P_M` keeps exactly the local degree-one functions | `S04_Lem4_05_PMFixesLocal.lean` | `L4_5_PMFixesLocal` | Characterizes fixed points of the matching-local projection. |
| proven | 4.6 | lemma | Local high-degree error formula | `S04_Lem4_06_LocalHighDegreeErrorFormula.lean` | `L4_6_LocalHighDegreeErrorFormula` | Identifies local projection error with average high-degree cube energy. |
| proven | 4.7 | lemma | High local degrees have zero inner product with local degree one | `S04_Lem4_07_PMPerpendicular.lean` | `L4_7_PMPerpendicular` | Orthogonality of local high-degree residuals to the local degree-one space. |
| proven | 4.8 | lemma | A basic indicator has local degree at most one | `S04_Lem4_08_TijLocalDegree.lean` | `L4_8_TijLocalDegree` | Each one-coset indicator restricts to local degree at most one. |
| proven | 4.9 | corollary | `U_1` is contained in every local degree-one space | `S04_Cor4_09_U1Local.lean` | `Cor4_9_U1Local` | Follows from Lemmas 4.5 and 4.8. |
| proven | 4.10 | theorem | Matching-cube spectral gap | `S04_Thm4_10_MatchingGap.lean` | `Thm4_10_MatchingGap` | Proved through the tableauDim Section 5 bridge. Lemma 5.32 assembles the Appendix A representation-theoretic inputs into the dimension-parameterized spectral model; the active route no longer carries the older `youngDim` dimension-branching typeclass hypotheses. |
| proven | 4.11 | lemma | One trial in cube coordinates | `S04_Lem4_11_TrialCubeCoordinates.lean` | `L4_11_TrialCubeCoordinates` | Rewrites one sampled group trial as the matching-cube square expression. |
| proven | 4.12 | proposition | Square energy controls global degree | `S04_Prop4_12_SquareEnergyControlsGlobalDegree.lean` | `Prop4_12_SquareEnergyControlsGlobalDegree` | Reduction from Theorem 4.10 to the one-trial square-energy lower bound. |
| proven | 4.13 | lemma | One-trial soundness | `S04_Lem4_13_OneTrialSoundness.lean` | `L4_13_OneTrialSoundness` | Combines Proposition 4.12 with the external Theorem 2.2 stability input and the rejection-probability lower bound. |
