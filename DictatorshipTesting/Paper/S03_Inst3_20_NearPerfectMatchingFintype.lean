import DictatorshipTesting.Paper.Defs.S03_Def3_19_NearPerfectMatching

/-!
Definition file for `nearPerfectMatchingFintype`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

noncomputable instance nearPerfectMatchingFintype (n : ℕ) :
    Fintype (NearPerfectMatching n) := by
  classical
  exact Fintype.ofInjective
    (fun M : NearPerfectMatching n => (M.left, M.right))
    (by
      intro M N h
      cases M
      cases N
      simp at h
      simp [h])

end DictatorshipTesting
