# Assumptions And Verification

The project has exactly two named mathematical assumptions. Both are the
literature inputs stated in Section 2 of the paper.

| Lean axiom | Paper statement | Reference |
| --- | --- | --- |
| `booleanU1_dictator_classification_input` | Theorem 2.1 | Filmus, *Boolean functions on S_n which are nearly linear*, Discrete Analysis 2021:25, Theorem 2.8 |
| `fknStability_input` | Theorem 2.2 | Filmus, same paper, Theorem 1.5 together with Theorem 2.8 |

The Section 5 Young action, Jucys--Murphy content action, degree-one block
identification, matching spectral bridge, finite certificates, and tester
amplification are ordinary Lean theorems.

Verification commands:

```bash
lake exe cache get
lake build DictatorshipTesting
rg "^axiom |sorry|opaque|unsafe" DictatorshipTesting
```
