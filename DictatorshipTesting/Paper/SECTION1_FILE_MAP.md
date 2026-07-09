# Section 1 File Map

Source checked: `../dictatorship_testing_soda27_latest.tex`.

Counting rule: theorem-like numbered environments only (`definition`, `lemma`,
`proposition`, `theorem`, `corollary`). Remarks, examples, equations, proofs,
and later-section statements are not represented here.

Section 1 statement count: 1.

| Status | Paper stmt | Environment | Paper title | Lean file | Main wrappers | Notes |
| --- | --- | --- | --- | --- | --- | --- |
| proven | 1.1 | theorem | Main theorem | `S01_Thm1_01_MainIntro.lean` | `Thm1_1_MainIntro` | Proved through the abstract tester-amplification wrapper `exists_dimensionFreeTester_of_oneTrialSoundness` and Lemma 4.11. Its active Lean dependencies include the Section 2 FKN/stability input and the Theorem 4.8 route documented in Section 4. Boolean `U_1` classification is not a direct dependency of this wrapper. |
