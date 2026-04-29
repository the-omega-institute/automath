import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.Zeta

/-- Concrete endpoint heat-probe moment sequence with one endpoint atom removed. -/
def xi_endpoint_heat_probe_rstar_root_ratio_moment
    (rStar mass endpoint : ℝ) (N : ℕ) : ℝ :=
  endpoint + mass * rStar ^ N

/-- The non-endpoint tail after subtracting the endpoint atom. -/
def xi_endpoint_heat_probe_rstar_root_ratio_tail
    (rStar mass endpoint : ℝ) (N : ℕ) : ℝ :=
  xi_endpoint_heat_probe_rstar_root_ratio_moment rStar mass endpoint N - endpoint

/-- Root estimator for the concrete one-radius endpoint tail. -/
noncomputable def xi_endpoint_heat_probe_rstar_root_ratio_rootEstimator
    (rStar mass : ℝ) (N : ℕ) : ℝ :=
  rStar * mass ^ (1 / (N + 1 : ℝ))

/-- Adjacent ratio of the endpoint tail. -/
noncomputable def xi_endpoint_heat_probe_rstar_root_ratio_ratio
    (rStar mass endpoint : ℝ) (N : ℕ) : ℝ :=
  xi_endpoint_heat_probe_rstar_root_ratio_tail rStar mass endpoint (N + 1) /
    xi_endpoint_heat_probe_rstar_root_ratio_tail rStar mass endpoint N

/-- Paper label: `thm:xi-endpoint-heat-probe-rstar-root-ratio`.  In the concrete
single-support-radius endpoint model, subtracting the endpoint atom leaves the nonnegative moment
tail `mass * rStar^N`; its root estimator and adjacent ratio both converge to `rStar`, and the
ratio is already exactly equal to `rStar` at every finite stage. -/
theorem paper_xi_endpoint_heat_probe_rstar_root_ratio
    (rStar mass endpoint : ℝ) (hrStar : 0 < rStar) (hmass : 0 < mass) :
    (∀ N : ℕ,
        xi_endpoint_heat_probe_rstar_root_ratio_tail rStar mass endpoint N =
          mass * rStar ^ N) ∧
      Tendsto (fun N : ℕ =>
        xi_endpoint_heat_probe_rstar_root_ratio_rootEstimator rStar mass N) atTop (𝓝 rStar) ∧
      (∀ N : ℕ,
        xi_endpoint_heat_probe_rstar_root_ratio_ratio rStar mass endpoint N = rStar) ∧
      Tendsto (fun N : ℕ =>
        xi_endpoint_heat_probe_rstar_root_ratio_ratio rStar mass endpoint N) atTop (𝓝 rStar) := by
  have htail :
      ∀ N : ℕ,
        xi_endpoint_heat_probe_rstar_root_ratio_tail rStar mass endpoint N =
          mass * rStar ^ N := by
    intro N
    simp [xi_endpoint_heat_probe_rstar_root_ratio_tail,
      xi_endpoint_heat_probe_rstar_root_ratio_moment]
  have hroot :
      Tendsto (fun N : ℕ =>
        xi_endpoint_heat_probe_rstar_root_ratio_rootEstimator rStar mass N) atTop (𝓝 rStar) := by
    have hpower :
        Tendsto (fun N : ℕ => mass ^ (1 / (N + 1 : ℝ))) atTop (𝓝 (mass ^ (0 : ℝ))) := by
      exact tendsto_const_nhds.rpow tendsto_one_div_add_atTop_nhds_zero_nat
        (Or.inl hmass.ne')
    have hmul :
        Tendsto (fun N : ℕ => rStar * mass ^ (1 / (N + 1 : ℝ))) atTop
          (𝓝 (rStar * mass ^ (0 : ℝ))) :=
      tendsto_const_nhds.mul hpower
    simpa [xi_endpoint_heat_probe_rstar_root_ratio_rootEstimator, Real.rpow_zero] using hmul
  have hratio :
      ∀ N : ℕ,
        xi_endpoint_heat_probe_rstar_root_ratio_ratio rStar mass endpoint N = rStar := by
    intro N
    have hden : mass * rStar ^ N ≠ 0 := by
      exact mul_ne_zero hmass.ne' (pow_ne_zero N hrStar.ne')
    calc
      xi_endpoint_heat_probe_rstar_root_ratio_ratio rStar mass endpoint N
          = (mass * rStar ^ (N + 1)) / (mass * rStar ^ N) := by
            simp [xi_endpoint_heat_probe_rstar_root_ratio_ratio, htail]
      _ = rStar := by
        rw [pow_succ]
        field_simp [hden, hmass.ne', pow_ne_zero N hrStar.ne']
  refine ⟨htail, hroot, hratio, ?_⟩
  have hfun :
      (fun N : ℕ => xi_endpoint_heat_probe_rstar_root_ratio_ratio rStar mass endpoint N) =
        fun _ : ℕ => rStar := by
    funext N
    exact hratio N
  rw [hfun]
  exact tendsto_const_nhds

end Omega.Zeta
