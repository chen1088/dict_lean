# Section 1 File Map

Source checked: `../dictatorship_testing_soda27_latest.tex`.

Counting rule: theorem-like numbered environments only (`definition`, `lemma`,
`proposition`, `theorem`, `corollary`). Remarks, examples, equations, proofs,
and later-section statements are not represented here.

Section 1 statement count: 1.

| Status | Paper stmt | Environment | Paper title | Lean file | Main wrappers | Notes |
| --- | --- | --- | --- | --- | --- | --- |
| proven | 1.1 | theorem | Main theorem | `S01_Thm1_01_MainIntro.lean` | `Thm1_1_MainIntro` | Constructs the operational four-query matching tester, proves perfect completeness from Lemma 3.2, and amplifies Lemma 4.11 by independent repetition. Ranks below four use a bounded exhaustive tester. Its active Lean dependencies include the Section 2 FKN/stability input and the Theorem 4.8 route documented in Section 4. |
