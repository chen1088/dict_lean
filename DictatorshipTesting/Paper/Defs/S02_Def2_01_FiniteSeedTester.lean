import DictatorshipTesting.Paper.Defs.S02_IntDef_DistToDictators
import AlgebraicLibrary.PropertyTesting

/-!
# Dictatorship-testing specialization of the generic oracle tester

The operational tester, probability API, and finite-seed lemmas live in
`AlgebraicLibrary`.  This module supplies only the permutation/Boolean and
dictator-property specialization used by the paper.
-/

noncomputable section

namespace DictatorshipTesting

/-- A paper tester is a generic tester whose queries are permutations and
whose oracle answers are Boolean. -/
abbrev OracleTester (α : Type*) [Fintype α] [DecidableEq α] :=
  AlgebraicLibrary.OracleTester (Perm α) Bool

namespace OracleTester

def run {α : Type*} [Fintype α] [DecidableEq α]
    (tester : OracleTester α) (f : BoolFn α) (seed : tester.Seed) : Bool :=
  AlgebraicLibrary.OracleTester.run tester f seed

def acceptanceProbability {α : Type*} [Fintype α] [DecidableEq α]
    (tester : OracleTester α) (f : BoolFn α) : ℝ :=
  AlgebraicLibrary.OracleTester.acceptanceProbability tester f

def rejectionProbability {α : Type*} [Fintype α] [DecidableEq α]
    (tester : OracleTester α) (f : BoolFn α) : ℝ :=
  AlgebraicLibrary.OracleTester.rejectionProbability tester f

def accepts {α : Type*} [Fintype α] [DecidableEq α]
    (tester : OracleTester α) (f : BoolFn α) : Prop :=
  tester.acceptanceProbability f = 1

def rejectsWithProbabilityAtLeast {α : Type*} [Fintype α] [DecidableEq α]
    (tester : OracleTester α) (f : BoolFn α) (p : ℝ) : Prop :=
  p ≤ tester.rejectionProbability f

def nonadaptive {α : Type*} [Fintype α] [DecidableEq α]
    (tester : OracleTester α) : Prop :=
  ∀ seed : tester.Seed,
    ∃ schedule : Fin tester.queryCount → Perm α, schedule = tester.query seed

/-- One-sidedness specialized to the paper's dictator property. -/
def oneSided {α : Type*} [Fintype α] [DecidableEq α]
    (tester : OracleTester α) : Prop :=
  ∀ f : BoolFn α, IsDictator f →
    ∀ seed : tester.Seed, tester.run f seed = true

theorem nonadaptive_of_operational {α : Type*} [Fintype α] [DecidableEq α]
    (tester : OracleTester α) : tester.nonadaptive :=
  AlgebraicLibrary.OracleTester.nonadaptive_of_operational tester

theorem seed_card_pos {α : Type*} [Fintype α] [DecidableEq α]
    (tester : OracleTester α) :
    0 < @Fintype.card tester.Seed tester.seedFintype :=
  AlgebraicLibrary.OracleTester.seed_card_pos tester

theorem acceptanceProbability_eq_one_of_run_true
    {α : Type*} [Fintype α] [DecidableEq α]
    (tester : OracleTester α) (f : BoolFn α)
    (h : ∀ seed : tester.Seed, tester.run f seed = true) :
    tester.acceptanceProbability f = 1 :=
  AlgebraicLibrary.OracleTester.acceptanceProbability_eq_one_of_run_true
    tester f h

theorem accepts_of_oneSided {α : Type*} [Fintype α] [DecidableEq α]
    (tester : OracleTester α) (h : tester.oneSided)
    (f : BoolFn α) (hf : IsDictator f) : tester.accepts f := by
  exact AlgebraicLibrary.OracleTester.accepts_of_oneSided
    tester IsDictator h f hf

theorem acceptance_add_rejection_probability
    {α : Type*} [Fintype α] [DecidableEq α]
    (tester : OracleTester α) (f : BoolFn α) :
    tester.acceptanceProbability f + tester.rejectionProbability f = 1 :=
  AlgebraicLibrary.OracleTester.acceptance_add_rejection_probability tester f

theorem rejectionProbability_eq_one_sub_acceptanceProbability
    {α : Type*} [Fintype α] [DecidableEq α]
    (tester : OracleTester α) (f : BoolFn α) :
    tester.rejectionProbability f = 1 - tester.acceptanceProbability f :=
  AlgebraicLibrary.OracleTester.rejectionProbability_eq_one_sub_acceptanceProbability
    tester f

theorem rejectionProbability_nonneg
    {α : Type*} [Fintype α] [DecidableEq α]
    (tester : OracleTester α) (f : BoolFn α) :
    0 ≤ tester.rejectionProbability f :=
  AlgebraicLibrary.OracleTester.rejectionProbability_nonneg tester f

theorem rejectionProbability_le_one
    {α : Type*} [Fintype α] [DecidableEq α]
    (tester : OracleTester α) (f : BoolFn α) :
    tester.rejectionProbability f ≤ 1 :=
  AlgebraicLibrary.OracleTester.rejectionProbability_le_one tester f

end OracleTester

end DictatorshipTesting
