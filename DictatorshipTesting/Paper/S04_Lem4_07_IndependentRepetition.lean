/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S01_Thm1_01_MainIntro`
-/
import DictatorshipTesting.Paper.Defs.S02_Def2_01_FiniteSeedTester
import DictatorshipTesting.Paper.Defs.S02_IntDef_IsDictator
import DictatorshipTesting.Paper.Defs.S02_IntDef_DistToDictators
import DictatorshipTesting.Paper.Defs.S03_IntDef_OneTrialRejectProbability
import DictatorshipTesting.Paper.S04_Lem4_06_OneTrialSoundness
import DictatorshipTesting.Paper.S03_Lem3_02_PerfectCompleteness

open AlgebraicLibrary

/-!
Paper statement: Lemma 4.7 (`lem:independent-repetition`).

The operational one-trial tester, independent repetition, amplification, and
small-dimension exhaustive tester are implemented here. Theorem 1.1 imports
this module and applies the resulting amplification theorem.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Random data used by one matching-cube trial. -/
abbrev MatchingTrialSeed (n : Nat) :=
  NearPerfectMatching n ×
    (Perm (Fin n) × CubeDirectionColor (n / 2))

/-- The four square corners queried by a matching-cube trial. -/
def matchingTrialQuery (n : Nat) (seed : MatchingTrialSeed n) :
    Fin 4 → Perm (Fin n) :=
  let M := seed.1.toOrdered
  let π := seed.2.1
  let c := seed.2.2
  ![π * M.tau (finCubeZero M.edgeCount),
    π * M.tau (cubeXor (finCubeZero M.edgeCount) (cubeColorU c)),
    π * M.tau (cubeXor (finCubeZero M.edgeCount) (cubeColorV c)),
    π * M.tau
      (cubeXor (cubeXor (finCubeZero M.edgeCount) (cubeColorU c))
        (cubeColorV c))]

/-- Accept exactly when the four Boolean answers have zero mixed second
difference. -/
def matchingTrialDecision (answers : Fin 4 → Bool) : Bool :=
  decide (boolToReal (answers 0) - boolToReal (answers 1) -
    boolToReal (answers 2) + boolToReal (answers 3) = 0)

/-- The operational four-query tester for one matching-cube trial. -/
def matchingTrialTester (n : Nat) : OracleTester (Fin n) where
  Seed := MatchingTrialSeed n
  seedFintype := inferInstance
  seedNonempty := inferInstance
  queryCount := 4
  query := matchingTrialQuery n
  decide := fun _seed => matchingTrialDecision

@[simp] theorem matchingTrialTester_queryCount (n : Nat) :
    (matchingTrialTester n).queryCount = 4 := by
  rfl

theorem matchingTrialTester_run_eq_decide_delta
    (n : Nat) (f : BoolFn (Fin n)) (seed : MatchingTrialSeed n) :
    (matchingTrialTester n).run f seed =
      decide (matchingTrialDelta f seed.1.toOrdered seed.2.1 seed.2.2 = 0) := by
  rfl

/-- One operational trial has exactly the rejection probability used in the
Section 4 soundness theorem. -/
theorem matchingTrialTester_rejectionProbability
    (n : Nat) (f : BoolFn (Fin n)) :
    (matchingTrialTester n).rejectionProbability f =
      oneTrialRejectProbability f := by
  classical
  have hindicator (M : NearPerfectMatching n) (π : Perm (Fin n))
      (c : CubeDirectionColor (n / 2)) :
      (if (matchingTrialTester n).run f (M, (π, c))
        then (0 : ℝ) else 1) =
      if matchingTrialDelta f M.toOrdered π c = 0 then (0 : ℝ) else 1 := by
    rw [matchingTrialTester_run_eq_decide_delta]
    by_cases hdelta : matchingTrialDelta f M.toOrdered π c = 0 <;>
      simp [hdelta]
  have hsum :
      (∑ seed : MatchingTrialSeed n,
        if (matchingTrialTester n).run f seed then (0 : ℝ) else 1) =
      ∑ M : NearPerfectMatching n,
        ∑ π : Perm (Fin n),
          ∑ c : CubeDirectionColor (n / 2),
            if matchingTrialDelta f M.toOrdered π c = 0
              then (0 : ℝ) else 1 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro M _hM
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro π _hπ
    apply Finset.sum_congr rfl
    intro c _hc
    exact hindicator M π c
  change
    (∑ seed : MatchingTrialSeed n,
      if (matchingTrialTester n).run f seed then (0 : ℝ) else 1) /
        (Fintype.card (MatchingTrialSeed n) : ℝ) = _
  rw [hsum]
  unfold oneTrialRejectProbability
  simp only [MatchingTrialSeed, Fintype.card_prod]
  push_cast
  simp_rw [← Finset.sum_div]
  ring

/-- Dictators are accepted on every seed of one matching-cube trial. -/
theorem matchingTrialTester_oneSided (n : Nat) :
    (matchingTrialTester n).oneSided := by
  intro f hf seed
  rw [matchingTrialTester_run_eq_decide_delta]
  simp [S03_Lem3_02_PerfectCompleteness f hf seed.1.toOrdered seed.2.1 seed.2.2]

/-- Independent repetition, accepting exactly when every trial accepts. -/
def repeatTester {α : Type*} [Fintype α] [DecidableEq α]
    (k : Nat) (tester : OracleTester α) : OracleTester α :=
  AlgebraicLibrary.repeatTester k tester

@[simp] theorem repeatTester_queryCount
    {α : Type*} [Fintype α] [DecidableEq α]
    (k : Nat) (tester : OracleTester α) :
    (repeatTester k tester).queryCount = k * tester.queryCount := by
  exact AlgebraicLibrary.repeatTester_queryCount k tester

@[simp] theorem repeatTester_run_zero
    {α : Type*} [Fintype α] [DecidableEq α]
    (tester : OracleTester α) (f : BoolFn α) (seed : (repeatTester 0 tester).Seed) :
    (repeatTester 0 tester).run f seed = true := by
  exact AlgebraicLibrary.repeatTester_run_zero tester f seed

@[simp] theorem repeatTester_run_succ
    {α : Type*} [Fintype α] [DecidableEq α]
    (k : Nat) (tester : OracleTester α) (f : BoolFn α)
    (seed : (repeatTester (k + 1) tester).Seed) :
    (repeatTester (k + 1) tester).run f seed =
      (tester.run f seed.1 && (repeatTester k tester).run f seed.2) := by
  exact AlgebraicLibrary.repeatTester_run_succ k tester f seed

theorem repeatTester_acceptanceProbability_succ
    {α : Type*} [Fintype α] [DecidableEq α]
    (k : Nat) (tester : OracleTester α) (f : BoolFn α) :
    (repeatTester (k + 1) tester).acceptanceProbability f =
      tester.acceptanceProbability f *
        (repeatTester k tester).acceptanceProbability f := by
  exact AlgebraicLibrary.repeatTester_acceptanceProbability_succ k tester f

theorem repeatTester_acceptanceProbability
    {α : Type*} [Fintype α] [DecidableEq α]
    (k : Nat) (tester : OracleTester α) (f : BoolFn α) :
    (repeatTester k tester).acceptanceProbability f =
      (tester.acceptanceProbability f) ^ k := by
  exact AlgebraicLibrary.repeatTester_acceptanceProbability k tester f

/-- Exact rejection probability under independent repetition. -/
theorem repeatTester_rejectionProbability
    {α : Type*} [Fintype α] [DecidableEq α]
    (k : Nat) (tester : OracleTester α) (f : BoolFn α) :
    (repeatTester k tester).rejectionProbability f =
      1 - (1 - tester.rejectionProbability f) ^ k := by
  exact AlgebraicLibrary.repeatTester_rejectionProbability k tester f

theorem repeatTester_oneSided
    {α : Type*} [Fintype α] [DecidableEq α]
    (k : Nat) (tester : OracleTester α) (h : tester.oneSided) :
    (repeatTester k tester).oneSided := by
  exact AlgebraicLibrary.repeatTester_oneSided IsDictator k tester h

/-- Query every permutation once and decide whether the resulting complete
truth table is a dictator.  This is used only in ranks below four. -/
def dictatorDecision {α : Type*} (f : BoolFn α) : Bool := by
  classical
  exact decide (IsDictator f)

def exhaustiveDictatorTester (n : Nat) : OracleTester (Fin n) where
  Seed := PUnit
  seedFintype := inferInstance
  seedNonempty := inferInstance
  queryCount := Fintype.card (Perm (Fin n))
  query := fun _seed => (Fintype.equivFin (Perm (Fin n))).symm
  decide := fun _seed answers =>
    dictatorDecision
      (fun π => answers (Fintype.equivFin (Perm (Fin n)) π))

theorem exhaustiveDictatorTester_run
    (n : Nat) (f : BoolFn (Fin n)) (seed : (exhaustiveDictatorTester n).Seed) :
    (exhaustiveDictatorTester n).run f seed = dictatorDecision f := by
  apply congrArg dictatorDecision
  funext π
  simp [exhaustiveDictatorTester]

theorem exhaustiveDictatorTester_oneSided (n : Nat) :
    (exhaustiveDictatorTester n).oneSided := by
  intro f hf seed
  rw [exhaustiveDictatorTester_run]
  simp [dictatorDecision, hf]

theorem exhaustiveDictatorTester_rejectionProbability_of_not_dictator
    (n : Nat) (f : BoolFn (Fin n)) (hf : ¬ IsDictator f) :
    (exhaustiveDictatorTester n).rejectionProbability f = 1 := by
  unfold OracleTester.rejectionProbability
  change (∑ seed : PUnit,
    if (exhaustiveDictatorTester n).run f seed then (0 : ℝ) else 1) /
      (Fintype.card PUnit : ℝ) = 1
  simp [exhaustiveDictatorTester_run, dictatorDecision, hf]

theorem exhaustiveDictatorTester_queryCount_le_six
    (n : Nat) (hn : n < 4) :
    (exhaustiveDictatorTester n).queryCount ≤ 6 := by
  change Fintype.card (Perm (Fin n)) ≤ 6
  rw [Fintype.card_perm, Fintype.card_fin]
  interval_cases n <;> norm_num [Nat.factorial]

/-- A dictator has distance at most zero from the dictator class. -/
theorem distToDictators_le_zero_of_dictator
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : BoolFn α) (hf : IsDictator f) :
    distToDictators f ≤ 0 := by
  let distances : Set ℝ :=
    {d : ℝ | ∃ g : BoolFn α, IsDictator g ∧ d = hammingDist f g}
  have hbdd : BddBelow distances := by
    refine ⟨0, ?_⟩
    intro d hd
    rcases hd with ⟨g, _hg, rfl⟩
    unfold hammingDist
    positivity
  have hzero : (0 : ℝ) ∈ distances := by
    refine ⟨f, hf, ?_⟩
    simp [hammingDist]
  unfold distToDictators
  change sInf distances ≤ 0
  exact csInf_le hbdd hzero

/-- Elementary reciprocal amplification bound. -/
theorem one_sub_pow_le_one_div_one_add_mul
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : Nat) :
    (1 - p) ^ k ≤ 1 / (1 + (k : ℝ) * p) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have hq : 0 ≤ 1 - p := by linarith
      have hd1 : 0 < 1 + (k : ℝ) * p := by positivity
      have hd2 : 0 < 1 + ((k + 1 : Nat) : ℝ) * p := by positivity
      rw [pow_succ]
      calc
        (1 - p) ^ k * (1 - p) ≤
            (1 / (1 + (k : ℝ) * p)) * (1 - p) :=
          mul_le_mul_of_nonneg_right ih hq
        _ ≤ 1 / (1 + ((k + 1 : Nat) : ℝ) * p) := by
          rw [show (1 / (1 + (k : ℝ) * p)) * (1 - p) =
            (1 - p) / (1 + (k : ℝ) * p) by ring]
          rw [div_le_div_iff₀ hd1 hd2]
          push_cast
          nlinarith [sq_nonneg p]

/-- Number of repetitions used for soundness amplification. -/
def amplificationRepeats (c0 ε : ℝ) : Nat :=
  Nat.ceil (2 / (c0 * ε ^ (2 : Nat)))

theorem amplificationRepeats_mul_lower
    (c0 ε p : ℝ) (hc0 : 0 < c0) (hε : 0 < ε)
    (hp : c0 * ε ^ (2 : Nat) ≤ p) :
    2 ≤ (amplificationRepeats c0 ε : ℝ) * p := by
  have hbase : 0 < c0 * ε ^ (2 : Nat) := by positivity
  have hceil : 2 / (c0 * ε ^ (2 : Nat)) ≤
      (amplificationRepeats c0 ε : ℝ) := by
    exact Nat.le_ceil _
  calc
    (2 : ℝ) = (2 / (c0 * ε ^ (2 : Nat))) *
        (c0 * ε ^ (2 : Nat)) := by field_simp
    _ ≤ (amplificationRepeats c0 ε : ℝ) *
        (c0 * ε ^ (2 : Nat)) :=
      mul_le_mul_of_nonneg_right hceil (le_of_lt hbase)
    _ ≤ (amplificationRepeats c0 ε : ℝ) * p :=
      mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)

theorem repeated_rejection_at_least_two_thirds
    {α : Type*} [Fintype α] [DecidableEq α]
    (tester : OracleTester α) (f : BoolFn α) (k : Nat)
    (hkp : 2 ≤ (k : ℝ) * tester.rejectionProbability f) :
    ((2 : ℝ) / 3) ≤ (repeatTester k tester).rejectionProbability f := by
  have hp0 := tester.rejectionProbability_nonneg f
  have hp1 := tester.rejectionProbability_le_one f
  have hpow := one_sub_pow_le_one_div_one_add_mul
    (tester.rejectionProbability f) hp0 hp1 k
  have hthird : 1 / (1 + (k : ℝ) * tester.rejectionProbability f) ≤
      (1 : ℝ) / 3 := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 1 +
      (k : ℝ) * tester.rejectionProbability f) (by norm_num : (0 : ℝ) < 3)).2
    nlinarith
  rw [repeatTester_rejectionProbability]
  linarith

theorem repeatedMatchingTester_query_bound
    (n : Nat) (c0 ε : ℝ) (hc0 : 0 < c0) (hε : 0 < ε) (hε1 : ε < 1) :
    ((repeatTester (amplificationRepeats c0 ε)
      (matchingTrialTester n)).queryCount : ℝ) ≤
        (10 + 8 / c0) * ε⁻¹ ^ (2 : Nat) := by
  let k := amplificationRepeats c0 ε
  have hx0 : 0 ≤ 2 / (c0 * ε ^ (2 : Nat)) := by positivity
  have hk : (k : ℝ) ≤ 2 / (c0 * ε ^ (2 : Nat)) + 1 := by
    exact le_of_lt (by
      simpa [k, amplificationRepeats] using Nat.ceil_lt_add_one hx0)
  have hinv : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).2 (le_of_lt hε1)
  have hinvSq : 1 ≤ ε⁻¹ ^ (2 : Nat) := one_le_pow₀ hinv
  have hx : 2 / (c0 * ε ^ (2 : Nat)) =
      (2 / c0) * ε⁻¹ ^ (2 : Nat) := by
    field_simp
  rw [repeatTester_queryCount, matchingTrialTester_queryCount]
  push_cast
  calc
    (k : ℝ) * 4 ≤ 4 * (2 / (c0 * ε ^ (2 : Nat)) + 1) := by
      nlinarith
    _ = (8 / c0) * ε⁻¹ ^ (2 : Nat) + 4 := by rw [hx]; ring
    _ ≤ (10 + 8 / c0) * ε⁻¹ ^ (2 : Nat) := by
      nlinarith

theorem exhaustiveDictatorTester_query_bound
    (n : Nat) (hn : n < 4) (c0 ε : ℝ)
    (hc0 : 0 < c0) (hε : 0 < ε) (hε1 : ε < 1) :
    ((exhaustiveDictatorTester n).queryCount : ℝ) ≤
      (10 + 8 / c0) * ε⁻¹ ^ (2 : Nat) := by
  have hq : ((exhaustiveDictatorTester n).queryCount : ℝ) ≤ 6 := by
    exact_mod_cast exhaustiveDictatorTester_queryCount_le_six n hn
  have hinv : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).2 (le_of_lt hε1)
  have hinvSq : 1 ≤ ε⁻¹ ^ (2 : Nat) := one_le_pow₀ hinv
  have hdiv : 0 < 8 / c0 := div_pos (by norm_num) hc0
  have hc : 10 < 10 + 8 / c0 := by linarith
  nlinarith

/-- A one-trial quadratic soundness bound yields the dimension-free one-sided
tester promised in the introduction. -/
theorem exists_dimensionFreeTester_of_oneTrialSoundness
    (htrial :
      ∃ c0 : ℝ, 0 < c0 ∧
        ∀ n : ℕ, 4 ≤ n → ∀ f : BoolFn (Fin n),
          c0 * (distToDictators f) ^ (2 : ℕ) ≤ oneTrialRejectProbability f) :
    ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, ∀ ε : ℝ, 0 < ε → ε < 1 →
        ∃ tester : OracleTester (Fin n),
          tester.nonadaptive ∧
          tester.oneSided ∧
          (tester.queryCount : ℝ) ≤ C * ε⁻¹ ^ (2 : ℕ) ∧
          (∀ f : BoolFn (Fin n), IsDictator f → tester.accepts f) ∧
          (∀ f : BoolFn (Fin n),
            ε ≤ distToDictators f →
              tester.rejectsWithProbabilityAtLeast f ((2 : ℝ) / 3)) := by
  rcases htrial with ⟨c0, hc0, htrial⟩
  refine ⟨10 + 8 / c0, by positivity, ?_⟩
  intro n ε hε hε1
  by_cases hn : 4 ≤ n
  · let k := amplificationRepeats c0 ε
    let tester := repeatTester k (matchingTrialTester n)
    refine ⟨tester, tester.nonadaptive_of_operational,
      repeatTester_oneSided k (matchingTrialTester n)
        (matchingTrialTester_oneSided n),
      ?_, ?_, ?_⟩
    · exact repeatedMatchingTester_query_bound n c0 ε hc0 hε hε1
    · intro f hf
      exact tester.accepts_of_oneSided
        (repeatTester_oneSided k (matchingTrialTester n)
          (matchingTrialTester_oneSided n)) f hf
    · intro f hfar
      unfold OracleTester.rejectsWithProbabilityAtLeast
      have hdistSq : ε ^ (2 : Nat) ≤ distToDictators f ^ (2 : Nat) := by
        nlinarith
      have hp : c0 * ε ^ (2 : Nat) ≤
          (matchingTrialTester n).rejectionProbability f := by
        rw [matchingTrialTester_rejectionProbability]
        exact (mul_le_mul_of_nonneg_left hdistSq (le_of_lt hc0)).trans
          (htrial n hn f)
      exact repeated_rejection_at_least_two_thirds
        (matchingTrialTester n) f k
        (amplificationRepeats_mul_lower c0 ε
          ((matchingTrialTester n).rejectionProbability f) hc0 hε hp)
  · have hnlt : n < 4 := by omega
    let tester := exhaustiveDictatorTester n
    refine ⟨tester, tester.nonadaptive_of_operational,
      exhaustiveDictatorTester_oneSided n, ?_, ?_, ?_⟩
    · exact exhaustiveDictatorTester_query_bound n hnlt c0 ε hc0 hε hε1
    · intro f hf
      exact tester.accepts_of_oneSided
        (exhaustiveDictatorTester_oneSided n) f hf
    · intro f hfar
      unfold OracleTester.rejectsWithProbabilityAtLeast
      have hnot : ¬ IsDictator f := by
        intro hf
        have hle := distToDictators_le_zero_of_dictator f hf
        linarith
      rw [exhaustiveDictatorTester_rejectionProbability_of_not_dictator n f hnot]
      norm_num


theorem S04_Lem4_07_repetition_rejection_probability
    {α : Type*} [Fintype α] [DecidableEq α]
    (k : Nat) (tester : OracleTester α) (f : BoolFn α) :
    (repeatTester k tester).rejectionProbability f =
      1 - (1 - tester.rejectionProbability f) ^ k :=
  repeatTester_rejectionProbability k tester f

theorem S04_Lem4_07_dimension_free_amplification
    (htrial :
      ∃ c0 : ℝ, 0 < c0 ∧
        ∀ n : ℕ, 4 ≤ n → ∀ f : BoolFn (Fin n),
          c0 * distToDictators f ^ (2 : ℕ) ≤ oneTrialRejectProbability f) :
    ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, ∀ ε : ℝ, 0 < ε → ε < 1 →
        ∃ tester : OracleTester (Fin n),
          tester.nonadaptive ∧ tester.oneSided ∧
          (tester.queryCount : ℝ) ≤ C * ε⁻¹ ^ (2 : ℕ) ∧
          (∀ f : BoolFn (Fin n), IsDictator f → tester.accepts f) ∧
          (∀ f : BoolFn (Fin n), ε ≤ distToDictators f →
            tester.rejectsWithProbabilityAtLeast f ((2 : ℝ) / 3)) :=
  exists_dimensionFreeTester_of_oneTrialSoundness htrial

end DictatorshipTesting
