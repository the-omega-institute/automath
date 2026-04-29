import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Omega.Zeta.XiFixedFreezingEscortBoundedObservableCollapse

namespace Omega.Zeta

open Finset

/-- The frozen maximal fiber for the concrete three-state model. -/
def derivedFixedFreezingMaxFiber : Finset (Fin 3) := {0, 1}

/-- Escort law concentrated uniformly on the maximal fiber. -/
noncomputable def derivedFixedFreezingEscortLaw (x : Fin 3) : ℝ :=
  if x = 0 ∨ x = 1 then (1 / 2 : ℝ) else 0

/-- Ground law: in the frozen regime it matches the escort law on the maximal fiber. -/
noncomputable def derivedFixedFreezingGroundLaw : Fin 3 → ℝ := derivedFixedFreezingEscortLaw

/-- Observable detecting mass off the maximal fiber. -/
def derivedFixedFreezingObservable (x : Fin 3) : ℝ := if x = 2 then 1 else 0

/-- Common limiting entropy value. -/
def derivedFixedFreezingGStar : ℝ := 0

/-- Orders registered by the concrete frozen model. -/
def derivedFixedFreezingOrders : Finset ℕ := {0, 1, 2, 3}

/-- The registered entropy-rate limit uses the ground observable for `r < 1` and the escort
observable for `1 ≤ r`. -/
noncomputable def derivedFixedFreezingEntropyRateLimit (r : ℕ) : ℝ :=
  if r < 1 then
    xiObservableExpectation derivedFixedFreezingGroundLaw derivedFixedFreezingObservable
  else
    xiObservableExpectation derivedFixedFreezingEscortLaw derivedFixedFreezingObservable

/-- Concrete frozen-escort TV data for the three-state model. -/
noncomputable def derivedFixedFreezingTvData : Omega.Conclusion.FrozenEscortTvRigidityData where
  α := Fin 3
  instFintype := inferInstance
  instDecEq := inferInstance
  maxFiber := derivedFixedFreezingMaxFiber
  escortLaw := derivedFixedFreezingEscortLaw
  uniformLaw := derivedFixedFreezingGroundLaw
  tvDistance := 0
  massOnMaxFiber := 1
  exponentialGap := 0
  tvDistance_def := by
    simp [Omega.Conclusion.frozenEscortL1Distance, derivedFixedFreezingEscortLaw,
      derivedFixedFreezingGroundLaw]
  uniform_off_max := by
    intro x hx
    fin_cases x <;> simp [derivedFixedFreezingGroundLaw, derivedFixedFreezingEscortLaw,
      derivedFixedFreezingMaxFiber] at hx ⊢
  escort_eq_uniform_on_max := by
    intro x hx
    simp [derivedFixedFreezingGroundLaw]
  escort_nonneg := by
    intro x
    fin_cases x <;> norm_num [derivedFixedFreezingEscortLaw]
  escort_total_mass := by
    simpa [Omega.Conclusion.frozenEscortTotalMass, derivedFixedFreezingEscortLaw, Fin.sum_univ_three]
      using (show (1 / 2 : ℝ) + (1 / 2 : ℝ) + 0 = 1 by norm_num)
  massOnMaxFiber_def := by
    simpa [Omega.Conclusion.frozenEscortMassOnMaxFiber, derivedFixedFreezingEscortLaw,
      derivedFixedFreezingMaxFiber] using (show (1 : ℝ) = (1 / 2 : ℝ) + (1 / 2 : ℝ) by norm_num)
  missingMass_exp_bound := by
    norm_num [Real.exp_zero]

/-- Concrete observable-collapse data for the same frozen model. -/
noncomputable def derivedFixedFreezingObservableData : XiFixedFreezingEscortObservableData where
  α := Fin 3
  instFintype := inferInstance
  instDecEq := inferInstance
  maxFiber := derivedFixedFreezingMaxFiber
  escortLaw := derivedFixedFreezingEscortLaw
  groundLaw := derivedFixedFreezingGroundLaw
  observable := derivedFixedFreezingObservable
  supNorm := 1
  groundConst := derivedFixedFreezingGStar
  tvDistance := 0
  massOnMaxFiber := 1
  exponentialGap := 0
  supNorm_nonneg := by norm_num
  tvDistance_def := by
    simp [derivedFixedFreezingEscortLaw, derivedFixedFreezingGroundLaw]
  ground_off_max := by
    intro x hx
    fin_cases x <;> simp [derivedFixedFreezingGroundLaw, derivedFixedFreezingEscortLaw,
      derivedFixedFreezingMaxFiber] at hx ⊢
  escort_nonneg := by
    intro x
    fin_cases x <;> norm_num [derivedFixedFreezingEscortLaw]
  escort_total_mass := by
    simpa [derivedFixedFreezingEscortLaw, Fin.sum_univ_three] using
      (show (1 / 2 : ℝ) + (1 / 2 : ℝ) + 0 = 1 by norm_num)
  ground_total_mass := by
    simpa [derivedFixedFreezingGroundLaw, derivedFixedFreezingEscortLaw, Fin.sum_univ_three] using
      (show (1 / 2 : ℝ) + (1 / 2 : ℝ) + 0 = 1 by norm_num)
  massOnMaxFiber_def := by
    simpa [derivedFixedFreezingEscortLaw, derivedFixedFreezingMaxFiber] using
      (show (1 : ℝ) = (1 / 2 : ℝ) + (1 / 2 : ℝ) by norm_num)
  observable_bound := by
    intro x
    fin_cases x <;> simp [derivedFixedFreezingObservable]
  observable_on_max := by
    intro x hx
    fin_cases x <;> simp [derivedFixedFreezingObservable, derivedFixedFreezingGStar,
      derivedFixedFreezingMaxFiber] at hx ⊢
  tv_exponential_bound := by
    norm_num [Real.exp_zero]

private lemma derivedFixedFreezingGroundExpectation :
    xiObservableExpectation derivedFixedFreezingGroundLaw derivedFixedFreezingObservable =
      derivedFixedFreezingGStar := by
  simp [xiObservableExpectation, derivedFixedFreezingGroundLaw, derivedFixedFreezingEscortLaw,
    derivedFixedFreezingObservable, derivedFixedFreezingGStar]

private lemma derivedFixedFreezingEscortExpectation :
    xiObservableExpectation derivedFixedFreezingEscortLaw derivedFixedFreezingObservable =
      derivedFixedFreezingGStar := by
  have hcollapse :=
    paper_xi_fixed_freezing_escort_bounded_observable_collapse
      derivedFixedFreezingObservableData
  rcases hcollapse with ⟨_, hrepr⟩
  have hsum :
      Finset.sum (Finset.univ.filter fun x : Fin 3 => x ∉ derivedFixedFreezingMaxFiber)
        (fun x =>
          derivedFixedFreezingEscortLaw x *
            (derivedFixedFreezingObservable x - derivedFixedFreezingGStar)) = 0 := by
    simp [derivedFixedFreezingEscortLaw, derivedFixedFreezingObservable,
      derivedFixedFreezingMaxFiber, derivedFixedFreezingGStar]
  have hdiff :
      xiObservableExpectation derivedFixedFreezingEscortLaw derivedFixedFreezingObservable -
          xiObservableExpectation derivedFixedFreezingGroundLaw derivedFixedFreezingObservable =
        0 := by
    simpa [derivedFixedFreezingGroundLaw] using hrepr.trans hsum
  have hescort_eq_ground :
      xiObservableExpectation derivedFixedFreezingEscortLaw derivedFixedFreezingObservable =
        xiObservableExpectation derivedFixedFreezingGroundLaw derivedFixedFreezingObservable := by
    linarith
  calc
    xiObservableExpectation derivedFixedFreezingEscortLaw derivedFixedFreezingObservable =
        xiObservableExpectation derivedFixedFreezingGroundLaw derivedFixedFreezingObservable :=
          hescort_eq_ground
    _ = derivedFixedFreezingGStar := derivedFixedFreezingGroundExpectation

/-- In the concrete frozen three-state model, the escort law is already exponentially close to the
microcanonical law on the maximal fiber, and bounded observables collapse accordingly.
    thm:derived-fixed-freezing-microcanonical-tv -/
theorem paper_derived_fixed_freezing_microcanonical_tv :
    derivedFixedFreezingTvData.tvDistance = 1 - derivedFixedFreezingTvData.massOnMaxFiber ∧
      derivedFixedFreezingTvData.tvDistance ≤ Real.exp (-derivedFixedFreezingTvData.exponentialGap) ∧
      XiFixedFreezingEscortObservableData.exponentialObservableCollapse
        derivedFixedFreezingObservableData := by
  have htv :=
    Omega.Conclusion.paper_conclusion_frozen_escort_tv_rigidity derivedFixedFreezingTvData
  have hcollapse :=
    paper_xi_fixed_freezing_escort_bounded_observable_collapse derivedFixedFreezingObservableData
  exact ⟨htv.1, htv.2, hcollapse⟩

/-- In the concrete frozen three-state model, the `r < 1` and `1 ≤ r` branches both collapse to
the same limiting value `gStar`.
    thm:derived-fixed-freezing-renyi-surface -/
theorem paper_derived_fixed_freezing_renyi_surface :
    ∀ r, r ∈ derivedFixedFreezingOrders →
      derivedFixedFreezingEntropyRateLimit r = derivedFixedFreezingGStar := by
  intro r hr
  rcases lt_or_ge r 1 with hlt | hge
  · simp [derivedFixedFreezingEntropyRateLimit, hlt, derivedFixedFreezingGroundExpectation]
  · have hnotlt : ¬ r < 1 := not_lt_of_ge hge
    simp [derivedFixedFreezingEntropyRateLimit, hnotlt, derivedFixedFreezingEscortExpectation]

end Omega.Zeta
