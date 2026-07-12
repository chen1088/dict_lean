import DictatorshipTesting.Paper.Defs.S02_IntDef_DistToDictators
/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.Defs.S02_IntDef_OneCosetReal`
- `DictatorshipTesting.Paper.S01_Thm1_01_MainIntro`
- `DictatorshipTesting.Paper.S04_Lem4_10_IndependentRepetitionAndAmplification`
-/


/-!
Definition file for operational finite-seed oracle testers.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- A finite-seed nonadaptive oracle tester.  For each random seed, all query
locations are fixed before any oracle answers are read. -/
structure OracleTester (α : Type*) [Fintype α] [DecidableEq α] where
  Seed : Type
  seedFintype : Fintype Seed
  seedNonempty : Nonempty Seed
  queryCount : ℕ
  query : Seed → Fin queryCount → Perm α
  decide : Seed → (Fin queryCount → Bool) → Bool

namespace OracleTester

/-- Execute a tester on one seed and one Boolean oracle.  `true` means accept. -/
def run {α : Type*} [Fintype α] [DecidableEq α]
    (tester : OracleTester α) (f : BoolFn α) (seed : tester.Seed) : Bool :=
  tester.decide seed (fun i => f (tester.query seed i))

/-- Uniform acceptance probability over the finite seed space. -/
def acceptanceProbability {α : Type*} [Fintype α] [DecidableEq α]
    (tester : OracleTester α) (f : BoolFn α) : ℝ := by
  letI := tester.seedFintype
  exact (∑ seed : tester.Seed,
    if tester.run f seed then (1 : ℝ) else 0) /
      (Fintype.card tester.Seed : ℝ)

/-- Uniform rejection probability over the finite seed space. -/
def rejectionProbability {α : Type*} [Fintype α] [DecidableEq α]
    (tester : OracleTester α) (f : BoolFn α) : ℝ := by
  letI := tester.seedFintype
  exact (∑ seed : tester.Seed,
    if tester.run f seed then (0 : ℝ) else 1) /
      (Fintype.card tester.Seed : ℝ)

/-- Semantic acceptance with probability one. -/
def accepts {α : Type*} [Fintype α] [DecidableEq α]
    (tester : OracleTester α) (f : BoolFn α) : Prop :=
  tester.acceptanceProbability f = 1

/-- Semantic lower bound on rejection probability. -/
def rejectsWithProbabilityAtLeast {α : Type*} [Fintype α] [DecidableEq α]
    (tester : OracleTester α) (f : BoolFn α) (p : ℝ) : Prop :=
  p ≤ tester.rejectionProbability f

/-- Nonadaptivity is structural: each seed determines one complete query
schedule, independently of the answer table. -/
def nonadaptive {α : Type*} [Fintype α] [DecidableEq α]
    (tester : OracleTester α) : Prop :=
  ∀ seed : tester.Seed,
    ∃ schedule : Fin tester.queryCount → Perm α,
      schedule = tester.query seed

/-- One-sidedness means every dictator is accepted for every seed. -/
def oneSided {α : Type*} [Fintype α] [DecidableEq α]
    (tester : OracleTester α) : Prop :=
  ∀ f : BoolFn α, IsDictator f →
    ∀ seed : tester.Seed, tester.run f seed = true

theorem nonadaptive_of_operational {α : Type*} [Fintype α] [DecidableEq α]
    (tester : OracleTester α) : tester.nonadaptive := by
  intro seed
  exact ⟨tester.query seed, rfl⟩

theorem seed_card_pos {α : Type*} [Fintype α] [DecidableEq α]
    (tester : OracleTester α) :
    0 < @Fintype.card tester.Seed tester.seedFintype := by
  letI := tester.seedFintype
  exact Fintype.card_pos_iff.mpr tester.seedNonempty

theorem acceptanceProbability_eq_one_of_run_true
    {α : Type*} [Fintype α] [DecidableEq α]
    (tester : OracleTester α) (f : BoolFn α)
    (h : ∀ seed : tester.Seed, tester.run f seed = true) :
    tester.acceptanceProbability f = 1 := by
  letI := tester.seedFintype
  unfold acceptanceProbability
  simp_rw [h]
  have hcard : (Fintype.card tester.Seed : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (tester.seed_card_pos))
  simp [hcard]

theorem accepts_of_oneSided {α : Type*} [Fintype α] [DecidableEq α]
    (tester : OracleTester α) (h : tester.oneSided)
    (f : BoolFn α) (hf : IsDictator f) : tester.accepts f := by
  exact acceptanceProbability_eq_one_of_run_true tester f (h f hf)

theorem acceptance_add_rejection_probability
    {α : Type*} [Fintype α] [DecidableEq α]
    (tester : OracleTester α) (f : BoolFn α) :
    tester.acceptanceProbability f + tester.rejectionProbability f = 1 := by
  letI := tester.seedFintype
  unfold acceptanceProbability rejectionProbability
  have hcard : (Fintype.card tester.Seed : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (tester.seed_card_pos))
  rw [← add_div]
  rw [← Finset.sum_add_distrib]
  have hsum :
      (∑ seed : tester.Seed,
        ((if tester.run f seed then (1 : ℝ) else 0) +
          if tester.run f seed then (0 : ℝ) else 1)) =
        Fintype.card tester.Seed := by
    calc
      _ = ∑ _seed : tester.Seed, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro seed _hseed
        cases tester.run f seed <;> simp
      _ = Fintype.card tester.Seed := by simp
  rw [hsum]
  exact div_self hcard

theorem rejectionProbability_eq_one_sub_acceptanceProbability
    {α : Type*} [Fintype α] [DecidableEq α]
    (tester : OracleTester α) (f : BoolFn α) :
    tester.rejectionProbability f = 1 - tester.acceptanceProbability f := by
  linarith [tester.acceptance_add_rejection_probability f]

theorem rejectionProbability_nonneg
    {α : Type*} [Fintype α] [DecidableEq α]
    (tester : OracleTester α) (f : BoolFn α) :
    0 ≤ tester.rejectionProbability f := by
  letI := tester.seedFintype
  unfold rejectionProbability
  positivity

theorem rejectionProbability_le_one
    {α : Type*} [Fintype α] [DecidableEq α]
    (tester : OracleTester α) (f : BoolFn α) :
    tester.rejectionProbability f ≤ 1 := by
  have ha : 0 ≤ tester.acceptanceProbability f := by
    letI := tester.seedFintype
    unfold acceptanceProbability
    positivity
  rw [tester.rejectionProbability_eq_one_sub_acceptanceProbability f]
  linarith

end OracleTester

end DictatorshipTesting
