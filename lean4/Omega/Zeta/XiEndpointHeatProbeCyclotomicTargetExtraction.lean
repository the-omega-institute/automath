import Mathlib
import Omega.Zeta.EndpointHeatProbeAdamsTwistRoots

namespace Omega.Zeta

open scoped BigOperators
open Classical Filter Topology

noncomputable section

/-- Finite weighted endpoint-heat probe mass built from the Adams-twist root kernel. -/
noncomputable def xiEndpointHeatProbeCyclotomicMass
    (S : Finset (Units Complex)) (μ : Units Complex → ℝ) (N d : ℕ) (ω : Units Complex) : ℝ :=
  Finset.sum S fun z => μ z * adamsTwistRootKernel N d ω z

/-- The atomic mass carried by the cyclotomic target set `Σ_{d,ω}`. -/
noncomputable def xiEndpointHeatProbeCyclotomicTargetMass
    (S : Finset (Units Complex)) (μ : Units Complex → ℝ) (d : ℕ) (ω : Units Complex) : ℝ :=
  Finset.sum S fun z => μ z * adamsTwistRootTargetValue d ω z

/-- Total weight off the cyclotomic target set `Σ_{d,ω}`. -/
noncomputable def xiEndpointHeatProbeCyclotomicResidualMass
    (S : Finset (Units Complex)) (μ : Units Complex → ℝ) (d : ℕ) (ω : Units Complex) : ℝ :=
  Finset.sum (Finset.filter (fun z => ¬ adamsTwistRootCondition d ω z) S) μ

set_option maxHeartbeats 400000 in
/-- The Adams-twisted endpoint kernel collapses the Toeplitz quadratic form to a pointwise
`r^N`-weight with `r = 1` on `Σ_{d,ω}` and `r = 1/2` off it. Summing over a finite atomic support
therefore gives a monotone sequence that converges to the mass on the cyclotomic target set.
`thm:xi-endpoint-heat-probe-cyclotomic-target-extraction` -/
theorem paper_xi_endpoint_heat_probe_cyclotomic_target_extraction
    (S : Finset (Units Complex)) (μ : Units Complex → ℝ) (d : ℕ) (ω : Units Complex)
    (hμ : ∀ z, 0 ≤ μ z) :
    (∀ N,
      xiEndpointHeatProbeCyclotomicTargetMass S μ d ω ≤
        xiEndpointHeatProbeCyclotomicMass S μ N d ω ∧
      xiEndpointHeatProbeCyclotomicMass S μ (N + 1) d ω ≤
        xiEndpointHeatProbeCyclotomicMass S μ N d ω ∧
      xiEndpointHeatProbeCyclotomicMass S μ N d ω =
        xiEndpointHeatProbeCyclotomicTargetMass S μ d ω +
          (1 / 2 : ℝ) ^ N * xiEndpointHeatProbeCyclotomicResidualMass S μ d ω) ∧
    Tendsto (fun N => xiEndpointHeatProbeCyclotomicMass S μ N d ω) atTop
      (nhds (xiEndpointHeatProbeCyclotomicTargetMass S μ d ω)) := by
  have hpointwise :
      ∀ N,
        xiEndpointHeatProbeCyclotomicTargetMass S μ d ω ≤
          xiEndpointHeatProbeCyclotomicMass S μ N d ω ∧
        xiEndpointHeatProbeCyclotomicMass S μ (N + 1) d ω ≤
          xiEndpointHeatProbeCyclotomicMass S μ N d ω ∧
        xiEndpointHeatProbeCyclotomicMass S μ N d ω =
          xiEndpointHeatProbeCyclotomicTargetMass S μ d ω +
            (1 / 2 : ℝ) ^ N * xiEndpointHeatProbeCyclotomicResidualMass S μ d ω := by
    intro N
    have hkernel := paper_xi_endpoint_heat_probe_adams_twist_roots N d (fun _ => 0) ω
    have htarget_le :
        xiEndpointHeatProbeCyclotomicTargetMass S μ d ω ≤
          xiEndpointHeatProbeCyclotomicMass S μ N d ω := by
      unfold xiEndpointHeatProbeCyclotomicTargetMass xiEndpointHeatProbeCyclotomicMass
      refine Finset.sum_le_sum ?_
      intro z hz
      exact mul_le_mul_of_nonneg_left (hkernel.2 z).2.2 (hμ z)
    have hmono :
        xiEndpointHeatProbeCyclotomicMass S μ (N + 1) d ω ≤
          xiEndpointHeatProbeCyclotomicMass S μ N d ω := by
      unfold xiEndpointHeatProbeCyclotomicMass
      refine Finset.sum_le_sum ?_
      intro z hz
      exact mul_le_mul_of_nonneg_left (hkernel.2 z).2.1 (hμ z)
    have htarget_filter :
        xiEndpointHeatProbeCyclotomicTargetMass S μ d ω =
          Finset.sum (Finset.filter (fun z => adamsTwistRootCondition d ω z) S) μ := by
      classical
      simp [xiEndpointHeatProbeCyclotomicTargetMass, adamsTwistRootTargetValue, Finset.sum_filter]
    have hresidual_sum :
        Finset.sum (Finset.filter (fun z => ¬ adamsTwistRootCondition d ω z) S)
            (fun z => μ z * (1 / 2 : ℝ) ^ N) =
          (1 / 2 : ℝ) ^ N * xiEndpointHeatProbeCyclotomicResidualMass S μ d ω := by
      unfold xiEndpointHeatProbeCyclotomicResidualMass
      calc
        Finset.sum (Finset.filter (fun z => ¬ adamsTwistRootCondition d ω z) S)
            (fun z => μ z * (1 / 2 : ℝ) ^ N) =
          Finset.sum (Finset.filter (fun z => ¬ adamsTwistRootCondition d ω z) S)
            (fun z => (1 / 2 : ℝ) ^ N * μ z) := by
              refine Finset.sum_congr rfl ?_
              intro z hz
              ring
        _ = (1 / 2 : ℝ) ^ N *
              Finset.sum (Finset.filter (fun z => ¬ adamsTwistRootCondition d ω z) S) μ := by
                simpa using
                  (Finset.mul_sum
                    (s := Finset.filter (fun z => ¬ adamsTwistRootCondition d ω z) S)
                    (f := μ) ((1 / 2 : ℝ) ^ N)).symm
    have hmass_split :
        xiEndpointHeatProbeCyclotomicMass S μ N d ω =
          Finset.sum (Finset.filter (fun z => adamsTwistRootCondition d ω z) S) μ +
            Finset.sum (Finset.filter (fun z => ¬ adamsTwistRootCondition d ω z) S)
              (fun z => μ z * (1 / 2 : ℝ) ^ N) := by
      classical
      unfold xiEndpointHeatProbeCyclotomicMass
      rw [← Finset.sum_filter_add_sum_filter_not S
        (fun z => adamsTwistRootCondition d ω z)
        (fun z => μ z * adamsTwistRootKernel N d ω z)]
      congr 1
      · refine Finset.sum_congr rfl ?_
        intro z hz
        have hz' : adamsTwistRootCondition d ω z := (Finset.mem_filter.mp hz).2
        simp [adamsTwistRootKernel, hz']
      · refine Finset.sum_congr rfl ?_
        intro z hz
        have hz' : ¬ adamsTwistRootCondition d ω z := (Finset.mem_filter.mp hz).2
        simp [adamsTwistRootKernel, hz']
    have hdecomp :
        xiEndpointHeatProbeCyclotomicMass S μ N d ω =
          xiEndpointHeatProbeCyclotomicTargetMass S μ d ω +
            (1 / 2 : ℝ) ^ N * xiEndpointHeatProbeCyclotomicResidualMass S μ d ω := by
      calc
        xiEndpointHeatProbeCyclotomicMass S μ N d ω =
            Finset.sum (Finset.filter (fun z => adamsTwistRootCondition d ω z) S) μ +
              Finset.sum (Finset.filter (fun z => ¬ adamsTwistRootCondition d ω z) S)
                (fun z => μ z * (1 / 2 : ℝ) ^ N) := hmass_split
        _ = xiEndpointHeatProbeCyclotomicTargetMass S μ d ω +
              Finset.sum (Finset.filter (fun z => ¬ adamsTwistRootCondition d ω z) S)
                (fun z => μ z * (1 / 2 : ℝ) ^ N) := by
                rw [← htarget_filter]
        _ = xiEndpointHeatProbeCyclotomicTargetMass S μ d ω +
              (1 / 2 : ℝ) ^ N * xiEndpointHeatProbeCyclotomicResidualMass S μ d ω := by
                rw [hresidual_sum]
    exact ⟨htarget_le, hmono, hdecomp⟩
  have hpow :
      Tendsto (fun N : ℕ =>
        (1 / 2 : ℝ) ^ N * xiEndpointHeatProbeCyclotomicResidualMass S μ d ω) atTop (nhds 0) := by
    have hbase :
        Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ N) atTop (nhds (0 : ℝ)) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using hbase.mul_const (xiEndpointHeatProbeCyclotomicResidualMass S μ d ω)
  have hlimit :
      Tendsto
        (fun N : ℕ =>
          xiEndpointHeatProbeCyclotomicTargetMass S μ d ω +
            (1 / 2 : ℝ) ^ N * xiEndpointHeatProbeCyclotomicResidualMass S μ d ω)
        atTop (nhds (xiEndpointHeatProbeCyclotomicTargetMass S μ d ω)) := by
    simpa using tendsto_const_nhds.add hpow
  have hfun :
      (fun N : ℕ => xiEndpointHeatProbeCyclotomicMass S μ N d ω) =
        (fun N : ℕ =>
          xiEndpointHeatProbeCyclotomicTargetMass S μ d ω +
            (1 / 2 : ℝ) ^ N * xiEndpointHeatProbeCyclotomicResidualMass S μ d ω) := by
    funext N
    exact (hpointwise N).2.2
  refine ⟨hpointwise, ?_⟩
  rw [hfun]
  exact hlimit

/-- The normalized tail from cyclotomic target extraction is exactly the constant residual mass
sequence. `thm:xi-endpoint-heat-probe-complement-radius-from-scalar-flow` -/
theorem paper_xi_endpoint_heat_probe_complement_radius_from_scalar_flow
    (S : Finset (Units Complex)) (μ : Units Complex → ℝ) (d : ℕ) (ω : Units Complex)
    (hμ : ∀ z, 0 ≤ μ z) :
    Tendsto
      (fun N : ℕ =>
        (xiEndpointHeatProbeCyclotomicMass S μ N d ω -
            xiEndpointHeatProbeCyclotomicTargetMass S μ d ω) /
          ((1 / 2 : ℝ) ^ N))
      atTop (nhds (xiEndpointHeatProbeCyclotomicResidualMass S μ d ω)) := by
  have hfun :
      (fun N : ℕ =>
        (xiEndpointHeatProbeCyclotomicMass S μ N d ω -
            xiEndpointHeatProbeCyclotomicTargetMass S μ d ω) /
          ((1 / 2 : ℝ) ^ N)) =
        fun _ => xiEndpointHeatProbeCyclotomicResidualMass S μ d ω := by
    funext N
    have hdecomp := ((paper_xi_endpoint_heat_probe_cyclotomic_target_extraction
      S μ d ω hμ).1 N).2.2
    have hpow_ne : ((1 / 2 : ℝ) ^ N) ≠ 0 := by
      positivity
    calc
      (xiEndpointHeatProbeCyclotomicMass S μ N d ω -
          xiEndpointHeatProbeCyclotomicTargetMass S μ d ω) /
          ((1 / 2 : ℝ) ^ N)
          =
        (((1 / 2 : ℝ) ^ N) * xiEndpointHeatProbeCyclotomicResidualMass S μ d ω) /
          ((1 / 2 : ℝ) ^ N) := by
            rw [hdecomp]
            ring
      _ = xiEndpointHeatProbeCyclotomicResidualMass S μ d ω := by
        field_simp [hpow_ne]
  rw [hfun]
  exact tendsto_const_nhds

end

end Omega.Zeta
