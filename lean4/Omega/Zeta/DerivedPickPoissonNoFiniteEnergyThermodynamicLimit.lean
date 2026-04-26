import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:derived-pick-poisson-no-finite-energy-thermodynamic-limit`. If the total
endpoint flux is at most linear in `κ` and a fixed pseudohyperbolic separation threshold
`ρ₀ < 1` feeds a quadratic entropy lower bound, then the Pick--Poisson determinant inherits the
explicit decay `detP ≤ C^κ ρ₀^(κ(κ - 1))`. -/
theorem paper_derived_pick_poisson_no_finite_energy_thermodynamic_limit
    (κ : ℕ) (C rho0 pSigma Sgen detP : ℝ) (hκ : 1 ≤ κ) (hC : 0 < C)
    (hrho0 : 0 < rho0 ∧ rho0 < 1) (hpSigma : 0 < pSigma) (hflux : pSigma ≤ C * (κ : ℝ))
    (hentropy :
      (κ : ℝ) * Real.log (κ : ℝ) - (κ : ℝ) * Real.log pSigma +
          (κ : ℝ) * ((κ : ℝ) - 1) * (-Real.log rho0) ≤
        Sgen)
    (hdet : detP = Real.exp (-Sgen)) :
    (-(κ : ℝ) * Real.log C + (κ : ℝ) * ((κ : ℝ) - 1) * (-Real.log rho0) ≤ Sgen) ∧
      detP ≤ C ^ κ * rho0 ^ (κ * (κ - 1)) := by
  have hκpos_nat : 0 < κ := lt_of_lt_of_le Nat.zero_lt_one hκ
  have hκpos : 0 < (κ : ℝ) := by exact_mod_cast hκpos_nat
  have hlog_flux : Real.log pSigma ≤ Real.log (C * (κ : ℝ)) :=
    Real.log_le_log hpSigma hflux
  have hlog_mul :
      Real.log (C * (κ : ℝ)) = Real.log C + Real.log (κ : ℝ) := by
    rw [Real.log_mul (ne_of_gt hC) (show (κ : ℝ) ≠ 0 by exact_mod_cast (ne_of_gt hκpos_nat))]
  have hfirst :
      -(κ : ℝ) * Real.log C ≤ (κ : ℝ) * Real.log (κ : ℝ) - (κ : ℝ) * Real.log pSigma := by
    rw [hlog_mul] at hlog_flux
    nlinarith [hlog_flux, show 0 ≤ (κ : ℝ) by positivity]
  have hlower :
      -(κ : ℝ) * Real.log C + (κ : ℝ) * ((κ : ℝ) - 1) * (-Real.log rho0) ≤ Sgen := by
    have hstep :
        -(κ : ℝ) * Real.log C + (κ : ℝ) * ((κ : ℝ) - 1) * (-Real.log rho0) ≤
          (κ : ℝ) * Real.log (κ : ℝ) - (κ : ℝ) * Real.log pSigma +
            (κ : ℝ) * ((κ : ℝ) - 1) * (-Real.log rho0) := by
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
      (κ : ℝ) * ((κ : ℝ) - 1) = ((κ * (κ - 1) : ℕ) : ℝ) := by
    calc
      (κ : ℝ) * ((κ : ℝ) - 1) = (κ : ℝ) * ((κ : ℝ) - ((1 : ℕ) : ℝ)) := by norm_num
      _ = (κ : ℝ) * ((κ - 1 : ℕ) : ℝ) := by rw [Nat.cast_sub hκ]
      _ = ((κ * (κ - 1) : ℕ) : ℝ) := by rw [Nat.cast_mul]
  have hdet_upper_exp :
      detP ≤ Real.exp ((κ : ℝ) * Real.log C + (κ : ℝ) * ((κ : ℝ) - 1) * Real.log rho0) := by
    rw [hdet]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hlower]
  refine ⟨hlower, ?_⟩
  calc
    detP ≤ Real.exp ((κ : ℝ) * Real.log C + (κ : ℝ) * ((κ : ℝ) - 1) * Real.log rho0) :=
      hdet_upper_exp
    _ = Real.exp ((κ : ℝ) * Real.log C) *
          Real.exp (((κ * (κ - 1) : ℕ) : ℝ) * Real.log rho0) := by
            rw [hkappa_mul, Real.exp_add]
    _ = C ^ κ * rho0 ^ (κ * (κ - 1)) := by rw [hpowC κ, hpowRho (κ * (κ - 1))]

end Omega.Zeta
