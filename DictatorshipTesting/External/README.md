# External formalization layer

This folder contains formalization attempts for the paper's external Appendix A
inputs.

Paper-facing files in `DictatorshipTesting/Paper/AppA_*` should eventually
become thin wrappers importing proofs from this folder.  Work here should not
hide incomplete arguments behind broad axioms: if a proof is incomplete, record
the exact missing bridge instead of packaging it as a new external theorem.

The current Appendix A target is A.2, the Jucys--Murphy content spectrum and
trace/scalar payload.  A.1 Young orthogonal realization is proved internally by
the type-A Coxeter normal-form construction in
`Paper/S05_Int_AdjacentCoxeterPresentation.lean`, and A.3 degree-one
Young-block identification is also proved internally.

Standard-tableau connectedness is no longer part of this external layer.  It is
proved internally as Section 5 Lemma 5.3.  Matching-average scalarity and its
global concrete weighted-energy identity are proved internally in Lemma 5.19.
