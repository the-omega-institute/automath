import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Omega.Zeta.XiPickPoissonSchurOneStepCollapse

namespace Omega.DerivedConsequences

open Omega.Zeta

/-- Paper label: `thm:derived-pick-poisson-schur-ledger-average-bottleneck`.
The one-step Schur-collapse package produces an averaged bottleneck index `m_*`, and the
previously formalized Pick--Poisson thermodynamic-limit estimate supplies the uniform-`ρ₀`
exponential decay corollary. -/
theorem paper_derived_pick_poisson_schur_ledger_average_bottleneck
    (kappaCollapse : ℕ) (hkappaCollapse : 0 < kappaCollapse)
    (pointWeight schurFlux : Fin kappaCollapse → ℝ) (geometricMeanEta interactionEnergy : ℝ)
    (witness : Fin kappaCollapse) (hpoint_pos : ∀ m, 0 < pointWeight m)
    (hschur_pos : ∀ m, 0 < schurFlux m) (hgeom_pos : 0 < geometricMeanEta)
    (hgeom_le : geometricMeanEta ≤ pointWeight witness / schurFlux witness)
    (henergy_eq : interactionEnergy = (kappaCollapse : ℝ) * Real.log geometricMeanEta)
    (kappaThermo : ℕ) (C rho0 pSigma Sgen detP : ℝ) (hkappaThermo : 1 ≤ kappaThermo)
    (hC : 0 < C) (hrho0 : 0 < rho0 ∧ rho0 < 1) (hpSigma : 0 < pSigma)
    (hflux : pSigma ≤ C * (kappaThermo : ℝ))
    (hentropy :
      (kappaThermo : ℝ) * Real.log (kappaThermo : ℝ) -
            (kappaThermo : ℝ) * Real.log pSigma +
          (kappaThermo : ℝ) * ((kappaThermo : ℝ) - 1) * (-Real.log rho0) ≤
        Sgen)
    (hdet : detP = Real.exp (-Sgen)) :
    (∃ m : Fin kappaCollapse,
      schurFlux m ≤ pointWeight m / geometricMeanEta ∧
        -Real.log (schurFlux m) ≥
          -Real.log (pointWeight m) + interactionEnergy / kappaCollapse) ∧
      (-(kappaThermo : ℝ) * Real.log C +
          (kappaThermo : ℝ) * ((kappaThermo : ℝ) - 1) * (-Real.log rho0) ≤
        Sgen) ∧
      detP ≤ C ^ kappaThermo * rho0 ^ (kappaThermo * (kappaThermo - 1)) := by
  let derived_pick_poisson_schur_ledger_average_bottleneck_data :
      XiPickPoissonSchurOneStepCollapseData := {
    kappa := kappaCollapse
    hkappa := hkappaCollapse
    pointWeight := pointWeight
    schurFlux := schurFlux
    geometricMeanEta := geometricMeanEta
    interactionEnergy := interactionEnergy
    witness := witness
    pointWeight_pos := hpoint_pos
    schurFlux_pos := hschur_pos
    geometricMeanEta_pos := hgeom_pos
    geometricMeanEta_le_witness := hgeom_le
    interactionEnergy_eq := henergy_eq
  }
  have hcollapse :
      derived_pick_poisson_schur_ledger_average_bottleneck_data.existsCollapseWitness :=
    paper_xi_pick_poisson_schur_one_step_collapse
      derived_pick_poisson_schur_ledger_average_bottleneck_data
  have hkappaThermo_pos_nat : 0 < kappaThermo := lt_of_lt_of_le Nat.zero_lt_one hkappaThermo
  have hlog_flux : Real.log pSigma ≤ Real.log (C * (kappaThermo : ℝ)) :=
    Real.log_le_log hpSigma hflux
  have hlog_mul :
      Real.log (C * (kappaThermo : ℝ)) = Real.log C + Real.log (kappaThermo : ℝ) := by
    rw [Real.log_mul (ne_of_gt hC)
      (show (kappaThermo : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hkappaThermo_pos_nat))]
  have hfirst :
      -(kappaThermo : ℝ) * Real.log C ≤
        (kappaThermo : ℝ) * Real.log (kappaThermo : ℝ) -
          (kappaThermo : ℝ) * Real.log pSigma := by
    rw [hlog_mul] at hlog_flux
    nlinarith [hlog_flux, show 0 ≤ (kappaThermo : ℝ) by positivity]
  have hlower :
      -(kappaThermo : ℝ) * Real.log C +
          (kappaThermo : ℝ) * ((kappaThermo : ℝ) - 1) * (-Real.log rho0) ≤
        Sgen := by
    have hstep :
        -(kappaThermo : ℝ) * Real.log C +
            (kappaThermo : ℝ) * ((kappaThermo : ℝ) - 1) * (-Real.log rho0) ≤
          (kappaThermo : ℝ) * Real.log (kappaThermo : ℝ) -
              (kappaThermo : ℝ) * Real.log pSigma +
            (kappaThermo : ℝ) * ((kappaThermo : ℝ) - 1) * (-Real.log rho0) := by
      nlinarith [hfirst]
    exact le_trans hstep hentropy
  have hpowC : ∀ n : ℕ, Real.exp ((n : ℝ) * Real.log C) = C ^ n := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ihn =>
        rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, Real.exp_add, Real.exp_log hC, ihn,
          pow_succ]
  have hpowRho : ∀ n : ℕ, Real.exp ((n : ℝ) * Real.log rho0) = rho0 ^ n := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ihn =>
        rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, Real.exp_add, Real.exp_log hrho0.1,
          ihn, pow_succ]
  have hkappa_mul :
      (kappaThermo : ℝ) * ((kappaThermo : ℝ) - 1) =
        ((kappaThermo * (kappaThermo - 1) : ℕ) : ℝ) := by
    calc
      (kappaThermo : ℝ) * ((kappaThermo : ℝ) - 1) =
          (kappaThermo : ℝ) * ((kappaThermo : ℝ) - ((1 : ℕ) : ℝ)) := by norm_num
      _ = (kappaThermo : ℝ) * ((kappaThermo - 1 : ℕ) : ℝ) := by rw [Nat.cast_sub hkappaThermo]
      _ = ((kappaThermo * (kappaThermo - 1) : ℕ) : ℝ) := by rw [Nat.cast_mul]
  have hdet_upper_exp :
      detP ≤
        Real.exp
          ((kappaThermo : ℝ) * Real.log C +
            (kappaThermo : ℝ) * ((kappaThermo : ℝ) - 1) * Real.log rho0) := by
    rw [hdet]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hlower]
  have hthermo :
      (-(kappaThermo : ℝ) * Real.log C +
          (kappaThermo : ℝ) * ((kappaThermo : ℝ) - 1) * (-Real.log rho0) ≤
        Sgen) ∧
        detP ≤ C ^ kappaThermo * rho0 ^ (kappaThermo * (kappaThermo - 1)) := by
    refine ⟨hlower, ?_⟩
    calc
      detP ≤
          Real.exp
            ((kappaThermo : ℝ) * Real.log C +
              (kappaThermo : ℝ) * ((kappaThermo : ℝ) - 1) * Real.log rho0) :=
        hdet_upper_exp
      _ = Real.exp ((kappaThermo : ℝ) * Real.log C) *
            Real.exp (((kappaThermo * (kappaThermo - 1) : ℕ) : ℝ) * Real.log rho0) := by
              rw [hkappa_mul, Real.exp_add]
      _ = C ^ kappaThermo * rho0 ^ (kappaThermo * (kappaThermo - 1)) := by
            rw [hpowC kappaThermo, hpowRho (kappaThermo * (kappaThermo - 1))]
  refine ⟨?_, hthermo.1, hthermo.2⟩
  rcases hcollapse with ⟨m, hm, hlogm⟩
  refine ⟨m, ?_, hlogm⟩
  simpa [xiPickPoissonCollapseFactor] using hm

end Omega.DerivedConsequences
