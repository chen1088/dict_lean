import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Finite-seed nonadaptive oracle testers

The query and answer types are parameters.  In particular, this API does not
know about permutations, Boolean functions, or dictators.
-/

noncomputable section

open scoped BigOperators

namespace AlgebraicLibrary

/-- A finite-seed nonadaptive oracle tester.  For each random seed, the whole
query schedule is fixed before any oracle answers are read. -/
structure OracleTester (Query : Type*) (Answer : Type*) where
  Seed : Type
  seedFintype : Fintype Seed
  seedNonempty : Nonempty Seed
  queryCount : ℕ
  query : Seed → Fin queryCount → Query
  decide : Seed → (Fin queryCount → Answer) → Bool

namespace OracleTester

/-- Execute a tester on one seed and one oracle.  `true` means accept. -/
def run {Query Answer : Type*} (tester : OracleTester Query Answer)
    (oracle : Query → Answer) (seed : tester.Seed) : Bool :=
  tester.decide seed (fun i => oracle (tester.query seed i))

/-- Uniform acceptance probability over the finite seed space. -/
def acceptanceProbability {Query Answer : Type*}
    (tester : OracleTester Query Answer) (oracle : Query → Answer) : ℝ := by
  letI := tester.seedFintype
  exact (∑ seed : tester.Seed,
    if tester.run oracle seed then (1 : ℝ) else 0) /
      (Fintype.card tester.Seed : ℝ)

/-- Uniform rejection probability over the finite seed space. -/
def rejectionProbability {Query Answer : Type*}
    (tester : OracleTester Query Answer) (oracle : Query → Answer) : ℝ := by
  letI := tester.seedFintype
  exact (∑ seed : tester.Seed,
    if tester.run oracle seed then (0 : ℝ) else 1) /
      (Fintype.card tester.Seed : ℝ)

/-- Semantic acceptance with probability one. -/
def accepts {Query Answer : Type*} (tester : OracleTester Query Answer)
    (oracle : Query → Answer) : Prop :=
  tester.acceptanceProbability oracle = 1

/-- Semantic lower bound on rejection probability. -/
def rejectsWithProbabilityAtLeast {Query Answer : Type*}
    (tester : OracleTester Query Answer) (oracle : Query → Answer) (p : ℝ) : Prop :=
  p ≤ tester.rejectionProbability oracle

/-- Nonadaptivity is structural in `OracleTester`: a seed determines the
complete query schedule independently of the answer table. -/
def nonadaptive {Query Answer : Type*} (tester : OracleTester Query Answer) : Prop :=
  ∀ seed : tester.Seed,
    ∃ schedule : Fin tester.queryCount → Query, schedule = tester.query seed

/-- A tester is one-sided for `Good` when it accepts every good oracle on every
seed.  The semantic property is deliberately supplied by the client. -/
def oneSided {Query Answer : Type*} (tester : OracleTester Query Answer)
    (Good : (Query → Answer) → Prop) : Prop :=
  ∀ oracle, Good oracle → ∀ seed : tester.Seed, tester.run oracle seed = true

theorem nonadaptive_of_operational {Query Answer : Type*}
    (tester : OracleTester Query Answer) : tester.nonadaptive := by
  intro seed
  exact ⟨tester.query seed, rfl⟩

theorem seed_card_pos {Query Answer : Type*} (tester : OracleTester Query Answer) :
    0 < @Fintype.card tester.Seed tester.seedFintype := by
  letI := tester.seedFintype
  exact Fintype.card_pos_iff.mpr tester.seedNonempty

theorem acceptanceProbability_eq_one_of_run_true {Query Answer : Type*}
    (tester : OracleTester Query Answer) (oracle : Query → Answer)
    (h : ∀ seed : tester.Seed, tester.run oracle seed = true) :
    tester.acceptanceProbability oracle = 1 := by
  letI := tester.seedFintype
  unfold acceptanceProbability
  simp_rw [h]
  have hcard : (Fintype.card tester.Seed : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt tester.seed_card_pos)
  simp [hcard]

theorem accepts_of_oneSided {Query Answer : Type*}
    (tester : OracleTester Query Answer) (Good : (Query → Answer) → Prop)
    (h : tester.oneSided Good) (oracle : Query → Answer) (horacle : Good oracle) :
    tester.accepts oracle := by
  exact acceptanceProbability_eq_one_of_run_true tester oracle (h oracle horacle)

theorem acceptance_add_rejection_probability {Query Answer : Type*}
    (tester : OracleTester Query Answer) (oracle : Query → Answer) :
    tester.acceptanceProbability oracle + tester.rejectionProbability oracle = 1 := by
  letI := tester.seedFintype
  unfold acceptanceProbability rejectionProbability
  have hcard : (Fintype.card tester.Seed : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt tester.seed_card_pos)
  rw [← add_div, ← Finset.sum_add_distrib]
  have hsum :
      (∑ seed : tester.Seed,
        ((if tester.run oracle seed then (1 : ℝ) else 0) +
          if tester.run oracle seed then (0 : ℝ) else 1)) =
        Fintype.card tester.Seed := by
    calc
      _ = ∑ _seed : tester.Seed, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro seed _
        cases tester.run oracle seed <;> simp
      _ = Fintype.card tester.Seed := by simp
  rw [hsum]
  exact div_self hcard

theorem rejectionProbability_eq_one_sub_acceptanceProbability
    {Query Answer : Type*} (tester : OracleTester Query Answer)
    (oracle : Query → Answer) :
    tester.rejectionProbability oracle = 1 - tester.acceptanceProbability oracle := by
  linarith [tester.acceptance_add_rejection_probability oracle]

theorem rejectionProbability_nonneg {Query Answer : Type*}
    (tester : OracleTester Query Answer) (oracle : Query → Answer) :
    0 ≤ tester.rejectionProbability oracle := by
  letI := tester.seedFintype
  unfold rejectionProbability
  positivity

theorem rejectionProbability_le_one {Query Answer : Type*}
    (tester : OracleTester Query Answer) (oracle : Query → Answer) :
    tester.rejectionProbability oracle ≤ 1 := by
  have ha : 0 ≤ tester.acceptanceProbability oracle := by
    letI := tester.seedFintype
    unfold acceptanceProbability
    positivity
  rw [tester.rejectionProbability_eq_one_sub_acceptanceProbability oracle]
  linarith

end OracleTester

end AlgebraicLibrary
