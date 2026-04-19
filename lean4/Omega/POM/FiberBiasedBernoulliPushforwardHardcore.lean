import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- Concrete finite fiber data for the biased Bernoulli pushforward and its hard-core posterior
description. The Bernoulli mass is stored as an explicit function together with the factorization
through the fiber statistic `reward`. -/
structure FiberBiasedBernoulliPushforwardHardcoreData where
  Ω : Type
  X : Type
  instFintypeΩ : Fintype Ω
  instDecidableEqΩ : DecidableEq Ω
  instFintypeX : Fintype X
  instDecidableEqX : DecidableEq X
  m : ℕ
  p : ℝ
  hp0 : 0 < p
  hp1 : p < 1
  fold : Ω → X
  oneCount : X → ℕ
  reward : Ω → ℕ
  bernoulliMass : Ω → ℝ
  fiberNonempty : ∀ x, Nonempty {ω // fold ω = x}
  IndependentSet : X → Type
  instFintypeIndependentSet : ∀ x, Fintype (IndependentSet x)
  fiberEquiv : ∀ x, {ω // fold ω = x} ≃ IndependentSet x
  independentSetCard : ∀ {x}, IndependentSet x → ℕ
  reward_eq_card : ∀ {x} (ω : {ω // fold ω = x}),
    reward ω.1 = independentSetCard (fiberEquiv x ω)
  mass_factorization : ∀ ω,
    bernoulliMass ω =
      (p ^ oneCount (fold ω)) * ((1 - p) ^ (m - oneCount (fold ω))) *
        ((p / (1 - p)) ^ reward ω)

attribute [instance] FiberBiasedBernoulliPushforwardHardcoreData.instFintypeΩ
attribute [instance] FiberBiasedBernoulliPushforwardHardcoreData.instDecidableEqΩ
attribute [instance] FiberBiasedBernoulliPushforwardHardcoreData.instFintypeX
attribute [instance] FiberBiasedBernoulliPushforwardHardcoreData.instDecidableEqX
attribute [instance] FiberBiasedBernoulliPushforwardHardcoreData.instFintypeIndependentSet

namespace FiberBiasedBernoulliPushforwardHardcoreData

/-- The hard-core activity induced by the Bernoulli bias. -/
noncomputable def activity (D : FiberBiasedBernoulliPushforwardHardcoreData) : ℝ :=
  D.p / (1 - D.p)

/-- The common factor on a fixed fiber after extracting the excess-weight term. -/
noncomputable def fiberWeight (D : FiberBiasedBernoulliPushforwardHardcoreData) (x : D.X) : ℝ :=
  (D.p ^ D.oneCount x) * ((1 - D.p) ^ (D.m - D.oneCount x))

/-- The fiber partition function `Z_x(t)`. -/
noncomputable def partitionFunction (D : FiberBiasedBernoulliPushforwardHardcoreData)
    (x : D.X) : ℝ :=
  ∑ ω : {ω // D.fold ω = x}, D.activity ^ D.reward ω.1

/-- The pushforward mass of the fiber label `x`. -/
noncomputable def pushforwardMass (D : FiberBiasedBernoulliPushforwardHardcoreData)
    (x : D.X) : ℝ :=
  ∑ ω : {ω // D.fold ω = x}, D.bernoulliMass ω.1

/-- The posterior on a fixed fiber. -/
noncomputable def posteriorMass (D : FiberBiasedBernoulliPushforwardHardcoreData)
    (x : D.X) (ω : {ω // D.fold ω = x}) : ℝ :=
  D.bernoulliMass ω.1 / D.pushforwardMass x

/-- The hard-core partition function after transporting the fiber along the canonical equivalence. -/
noncomputable def independentSetPartitionFunction (D : FiberBiasedBernoulliPushforwardHardcoreData)
    (x : D.X) : ℝ :=
  ∑ S : D.IndependentSet x, D.activity ^ D.independentSetCard S

/-- The hard-core mass of an independent set. -/
noncomputable def hardcoreMass (D : FiberBiasedBernoulliPushforwardHardcoreData)
    (x : D.X) (S : D.IndependentSet x) : ℝ :=
  D.activity ^ D.independentSetCard S / D.independentSetPartitionFunction x

/-- The transported posterior on the independent-set side. -/
noncomputable def posteriorOnIndependentSet (D : FiberBiasedBernoulliPushforwardHardcoreData)
    (x : D.X) (S : D.IndependentSet x) : ℝ :=
  D.posteriorMass x ((D.fiberEquiv x).symm S)

/-- Closed form for the pushforward mass. -/
def pushforwardClosedForm (D : FiberBiasedBernoulliPushforwardHardcoreData) : Prop :=
  ∀ x, D.pushforwardMass x = D.fiberWeight x * D.partitionFunction x

/-- Closed form for the fiber posterior. -/
def posteriorHardcoreForm (D : FiberBiasedBernoulliPushforwardHardcoreData) : Prop :=
  ∀ x (ω : {ω // D.fold ω = x}),
    D.posteriorMass x ω = D.activity ^ D.reward ω.1 / D.partitionFunction x

/-- The fiber posterior matches the hard-core model under the canonical fiber-to-independent-set
equivalence. -/
def posteriorMatchesIndependentSetModel (D : FiberBiasedBernoulliPushforwardHardcoreData) : Prop :=
  ∀ x (S : D.IndependentSet x), D.posteriorOnIndependentSet x S = D.hardcoreMass x S

lemma activity_pos (D : FiberBiasedBernoulliPushforwardHardcoreData) : 0 < D.activity := by
  unfold activity
  have hp' : 0 < 1 - D.p := sub_pos.mpr D.hp1
  exact div_pos D.hp0 hp'

lemma fiberWeight_pos (D : FiberBiasedBernoulliPushforwardHardcoreData) (x : D.X) :
    0 < D.fiberWeight x := by
  unfold fiberWeight
  have hp' : 0 < 1 - D.p := sub_pos.mpr D.hp1
  exact mul_pos (pow_pos D.hp0 _) (pow_pos hp' _)

lemma partitionFunction_pos (D : FiberBiasedBernoulliPushforwardHardcoreData) (x : D.X) :
    0 < D.partitionFunction x := by
  classical
  obtain ⟨ω⟩ := D.fiberNonempty x
  have hterm :
      0 < D.activity ^ D.reward ω.1 := by
    exact pow_pos D.activity_pos _
  have hle :
      D.activity ^ D.reward ω.1 ≤ D.partitionFunction x := by
    unfold partitionFunction
    exact Finset.single_le_sum
      (f := fun ω : {ω // D.fold ω = x} => D.activity ^ D.reward ω.1)
      (fun _ _ => le_of_lt (pow_pos D.activity_pos _))
      (Finset.mem_univ ω)
  exact lt_of_lt_of_le hterm hle

lemma independentSetPartition_eq_partitionFunction
    (D : FiberBiasedBernoulliPushforwardHardcoreData) (x : D.X) :
    D.independentSetPartitionFunction x = D.partitionFunction x := by
  symm
  unfold independentSetPartitionFunction partitionFunction
  refine Fintype.sum_equiv (D.fiberEquiv x)
    (fun ω : {ω // D.fold ω = x} => D.activity ^ D.reward ω.1)
    (fun S : D.IndependentSet x => D.activity ^ D.independentSetCard S) ?_
  intro ω
  simp [D.reward_eq_card]

end FiberBiasedBernoulliPushforwardHardcoreData

open FiberBiasedBernoulliPushforwardHardcoreData

/-- Expanding each fiber mass as a common Bernoulli factor times the activity monomial gives the
pushforward closed form; dividing by the fiber partition function produces the hard-core posterior,
and the canonical fiber-to-independent-set equivalence transports it to the independent-set model.
    thm:pom-fiber-biased-bernoulli-pushforward-hardcore -/
theorem paper_pom_fiber_biased_bernoulli_pushforward_hardcore
    (D : FiberBiasedBernoulliPushforwardHardcoreData) :
    D.pushforwardClosedForm ∧ D.posteriorHardcoreForm ∧ D.posteriorMatchesIndependentSetModel := by
  have hpush : D.pushforwardClosedForm := by
    intro x
    unfold pushforwardMass partitionFunction fiberWeight
    calc
      ∑ ω : {ω // D.fold ω = x}, D.bernoulliMass ω.1
          = ∑ ω : {ω // D.fold ω = x},
              ((D.p ^ D.oneCount x) * ((1 - D.p) ^ (D.m - D.oneCount x))) *
                (D.activity ^ D.reward ω.1) := by
                  refine Finset.sum_congr rfl ?_
                  intro ω _
                  rw [D.mass_factorization ω.1]
                  simp [activity, ω.2]
      _ = ((D.p ^ D.oneCount x) * ((1 - D.p) ^ (D.m - D.oneCount x))) *
            ∑ ω : {ω // D.fold ω = x}, D.activity ^ D.reward ω.1 := by
              rw [Finset.mul_sum]
  have hpost : D.posteriorHardcoreForm := by
    intro x ω
    have hbase_pos : 0 < D.fiberWeight x := D.fiberWeight_pos x
    have hpart_pos : 0 < D.partitionFunction x := D.partitionFunction_pos x
    have hbase_ne : D.fiberWeight x ≠ 0 := hbase_pos.ne'
    calc
      D.posteriorMass x ω
          = (D.fiberWeight x * D.activity ^ D.reward ω.1) /
              (D.fiberWeight x * D.partitionFunction x) := by
                unfold posteriorMass
                rw [D.mass_factorization ω.1, hpush x]
                simp [fiberWeight, activity, ω.2]
      _ = D.activity ^ D.reward ω.1 / D.partitionFunction x := by
            field_simp [hbase_ne, hpart_pos.ne']
  have hmatch : D.posteriorMatchesIndependentSetModel := by
    intro x S
    have hcard :
        D.reward ((D.fiberEquiv x).symm S).1 = D.independentSetCard S := by
      simpa using D.reward_eq_card ((D.fiberEquiv x).symm S)
    unfold posteriorOnIndependentSet hardcoreMass
    rw [hpost x ((D.fiberEquiv x).symm S), hcard, D.independentSetPartition_eq_partitionFunction]
  exact ⟨hpush, hpost, hmatch⟩

end Omega.POM
