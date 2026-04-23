import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Omega.Zeta.DerivedPickPoissonClusteredQuadraticCoerciveLowerBound

namespace Omega.Zeta

/-- Paper label: `thm:derived-pick-poisson-fixed-flux-uniform-separation-quadratic-collapse`.
The clustered quadratic coercive lower bound controls the entropy side, and the previously
formalized fixed-flux / uniform-separation determinant estimate then exponentiates this lower
bound into the explicit Pick--Poisson collapse. -/
theorem paper_derived_pick_poisson_fixed_flux_uniform_separation_quadratic_collapse
    (κ : ℕ) (C rho0 pSigma Sgen detP : ℝ)
    (kappa1 kappa2 kappa3 interaction12 interaction13 interaction23 : ℝ)
    (hκ : 1 ≤ κ) (hC : 0 < C) (hrho0 : 0 < rho0 ∧ rho0 < 1) (hpSigma : 0 < pSigma)
    (hflux : pSigma ≤ C * (κ : ℝ))
    (hinteraction12 : rho0 * kappa1 * kappa2 ≤ interaction12)
    (hinteraction13 : rho0 * kappa1 * kappa3 ≤ interaction13)
    (hinteraction23 : rho0 * kappa2 * kappa3 ≤ interaction23)
    (hdefectEntropy :
      Sgen =
        (kappa1 ^ 2 + kappa2 ^ 2 + kappa3 ^ 2) +
          2 * (interaction12 + interaction13 + interaction23))
    (hentropy :
      (κ : ℝ) * Real.log (κ : ℝ) - (κ : ℝ) * Real.log pSigma +
          (κ : ℝ) * ((κ : ℝ) - 1) * (-Real.log rho0) ≤
        Sgen)
    (hdet : detP = Real.exp (-Sgen)) :
    rho0 * (kappa1 + kappa2 + kappa3) ^ 2 +
        (1 - rho0) * (kappa1 ^ 2 + kappa2 ^ 2 + kappa3 ^ 2) ≤
      Sgen ∧
      (-(κ : ℝ) * Real.log C + (κ : ℝ) * ((κ : ℝ) - 1) * (-Real.log rho0) ≤ Sgen) ∧
      detP ≤ C ^ κ * rho0 ^ (κ * (κ - 1)) := by
  let D : PickPoissonClusteredQuadraticCoerciveData := {
    kappa1 := kappa1
    kappa2 := kappa2
    kappa3 := kappa3
    rho0 := rho0
    interaction12 := interaction12
    interaction13 := interaction13
    interaction23 := interaction23
    defectEntropy := Sgen
    hinteraction12 := hinteraction12
    hinteraction13 := hinteraction13
    hinteraction23 := hinteraction23
    hdefectEntropy := hdefectEntropy
  }
  have hquadratic :
      rho0 * (kappa1 + kappa2 + kappa3) ^ 2 +
          (1 - rho0) * (kappa1 ^ 2 + kappa2 ^ 2 + kappa3 ^ 2) ≤
        Sgen := by
    simpa [D, PickPoissonClusteredQuadraticCoerciveLowerBoundStatement, clusteredTotalKappa,
      clusteredSumSquares] using
      paper_derived_pick_poisson_clustered_quadratic_coercive_lower_bound D
  have hκpos_nat : 0 < κ := lt_of_lt_of_le Nat.zero_lt_one hκ
  have hlog_flux : Real.log pSigma ≤ Real.log (C * (κ : ℝ)) :=
    Real.log_le_log hpSigma hflux
  have hlog_mul :
      Real.log (C * (κ : ℝ)) = Real.log C + Real.log (κ : ℝ) := by
    rw [Real.log_mul (ne_of_gt hC)
      (show (κ : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hκpos_nat))]
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
  refine ⟨hquadratic, hlower, ?_⟩
  calc
    detP ≤ Real.exp ((κ : ℝ) * Real.log C + (κ : ℝ) * ((κ : ℝ) - 1) * Real.log rho0) :=
      hdet_upper_exp
    _ = Real.exp ((κ : ℝ) * Real.log C) *
          Real.exp (((κ * (κ - 1) : ℕ) : ℝ) * Real.log rho0) := by
            rw [hkappa_mul, Real.exp_add]
    _ = C ^ κ * rho0 ^ (κ * (κ - 1)) := by rw [hpowC κ, hpowRho (κ * (κ - 1))]

end Omega.Zeta
