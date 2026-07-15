import AlgebraicLibrary.PropertyTesting.Basic

/-! Independent repetition of finite-seed oracle testers. -/

noncomputable section

open scoped BigOperators

namespace AlgebraicLibrary

/-- Repeat a tester independently `k` times, accepting exactly when every trial
accepts. -/
def repeatTester {Query Answer : Type*} (k : ℕ)
    (tester : OracleTester Query Answer) : OracleTester Query Answer :=
  match k with
  | 0 =>
      { Seed := PUnit
        seedFintype := inferInstance
        seedNonempty := inferInstance
        queryCount := 0
        query := fun _seed i => Fin.elim0 i
        decide := fun _seed _answers => true }
  | k + 1 =>
      let rest := repeatTester k tester
      { Seed := tester.Seed × rest.Seed
        seedFintype := by
          letI := tester.seedFintype
          letI := rest.seedFintype
          infer_instance
        seedNonempty := Nonempty.map2 Prod.mk tester.seedNonempty rest.seedNonempty
        queryCount := tester.queryCount + rest.queryCount
        query := fun seed =>
          Fin.addCases (tester.query seed.1) (rest.query seed.2)
        decide := fun seed answers =>
          tester.decide seed.1
              (fun i => answers (Fin.castAdd rest.queryCount i)) &&
            rest.decide seed.2
              (fun i => answers (Fin.natAdd tester.queryCount i)) }

@[simp] theorem repeatTester_queryCount {Query Answer : Type*} (k : ℕ)
    (tester : OracleTester Query Answer) :
    (repeatTester k tester).queryCount = k * tester.queryCount := by
  induction k with
  | zero => simp [repeatTester]
  | succ k ih => simp [repeatTester, ih, Nat.succ_mul, Nat.add_comm]

@[simp] theorem repeatTester_run_zero {Query Answer : Type*}
    (tester : OracleTester Query Answer) (oracle : Query → Answer)
    (seed : (repeatTester 0 tester).Seed) :
    (repeatTester 0 tester).run oracle seed = true := by
  rfl

@[simp] theorem repeatTester_run_succ {Query Answer : Type*} (k : ℕ)
    (tester : OracleTester Query Answer) (oracle : Query → Answer)
    (seed : (repeatTester (k + 1) tester).Seed) :
    (repeatTester (k + 1) tester).run oracle seed =
      (tester.run oracle seed.1 && (repeatTester k tester).run oracle seed.2) := by
  simp [OracleTester.run, repeatTester, Fin.addCases]

theorem repeatTester_acceptanceProbability_succ {Query Answer : Type*} (k : ℕ)
    (tester : OracleTester Query Answer) (oracle : Query → Answer) :
    (repeatTester (k + 1) tester).acceptanceProbability oracle =
      tester.acceptanceProbability oracle *
        (repeatTester k tester).acceptanceProbability oracle := by
  classical
  let rest := repeatTester k tester
  letI := tester.seedFintype
  letI := rest.seedFintype
  change (repeatTester (k + 1) tester).acceptanceProbability oracle =
    tester.acceptanceProbability oracle * rest.acceptanceProbability oracle
  have hindicator (s : tester.Seed) (t : rest.Seed) :
      (if (repeatTester (k + 1) tester).run oracle (s, t)
        then (1 : ℝ) else 0) =
      (if tester.run oracle s then (1 : ℝ) else 0) *
        (if rest.run oracle t then (1 : ℝ) else 0) := by
    rw [repeatTester_run_succ]
    cases tester.run oracle s <;> cases rest.run oracle t <;> norm_num
  unfold OracleTester.acceptanceProbability
  change
    (∑ seed : tester.Seed × rest.Seed,
      if (repeatTester (k + 1) tester).run oracle seed then (1 : ℝ) else 0) /
        (Fintype.card (tester.Seed × rest.Seed) : ℝ) = _
  rw [Fintype.sum_prod_type]
  simp_rw [hindicator]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  simp only [Fintype.card_prod]
  push_cast
  have hcardTester : (Fintype.card tester.Seed : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt tester.seed_card_pos)
  have hcardRest : (Fintype.card rest.Seed : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt rest.seed_card_pos)
  field_simp

theorem repeatTester_acceptanceProbability {Query Answer : Type*} (k : ℕ)
    (tester : OracleTester Query Answer) (oracle : Query → Answer) :
    (repeatTester k tester).acceptanceProbability oracle =
      (tester.acceptanceProbability oracle) ^ k := by
  induction k with
  | zero =>
      change (∑ _seed : PUnit, (1 : ℝ)) / (Fintype.card PUnit : ℝ) = 1
      norm_num
  | succ k ih =>
      rw [repeatTester_acceptanceProbability_succ, ih, pow_succ]
      ring

/-- Exact rejection probability under independent repetition. -/
theorem repeatTester_rejectionProbability {Query Answer : Type*} (k : ℕ)
    (tester : OracleTester Query Answer) (oracle : Query → Answer) :
    (repeatTester k tester).rejectionProbability oracle =
      1 - (1 - tester.rejectionProbability oracle) ^ k := by
  rw [(repeatTester k tester).rejectionProbability_eq_one_sub_acceptanceProbability]
  rw [repeatTester_acceptanceProbability]
  have ha : tester.acceptanceProbability oracle =
      1 - tester.rejectionProbability oracle := by
    linarith [tester.acceptance_add_rejection_probability oracle]
  rw [ha]

theorem repeatTester_oneSided {Query Answer : Type*} (Good : (Query → Answer) → Prop)
    (k : ℕ) (tester : OracleTester Query Answer) (h : tester.oneSided Good) :
    (repeatTester k tester).oneSided Good := by
  intro oracle horacle
  induction k with
  | zero =>
      intro seed
      exact repeatTester_run_zero tester oracle seed
  | succ k ih =>
      intro seed
      rw [repeatTester_run_succ, h oracle horacle seed.1, ih seed.2]
      rfl

end AlgebraicLibrary
