import Omega.SyncKernelWeighted.WeightedXiSingleExceptionPair

namespace Omega.SyncKernelWeighted

/-- Paper-facing package for the three reciprocal quadratics attached to the completed weighted
`Ξ` numerator: two critical-line factors encoded by angle parameters and one exceptional real
factor encoded by the off-critical coordinate `α > 1`. -/
def sync_kernel_weighted_xi_three_quadratics_statement : Prop :=
  ∃ t1 t2 t3 α β θ1 θ2 : ℝ,
    -2 < t1 ∧
      t1 < -1 ∧
      sync_kernel_weighted_xi_single_exception_pair_P t1 = 0 ∧
      -1 < t2 ∧
      t2 < 0 ∧
      sync_kernel_weighted_xi_single_exception_pair_P t2 = 0 ∧
      3 < t3 ∧
      t3 < 4 ∧
      sync_kernel_weighted_xi_single_exception_pair_P t3 = 0 ∧
      α = sync_kernel_weighted_xi_single_exception_pair_alpha t3 ∧
      β = sync_kernel_weighted_xi_exception_coordinate_beta α ∧
      1 < α ∧
      α ^ (2 : ℕ) - t3 * α + 1 = 0 ∧
      α + α⁻¹ = t3 ∧
      sync_kernel_weighted_xi_single_exception_pair_N α = 0 ∧
      sync_kernel_weighted_xi_single_exception_pair_N α⁻¹ = 0 ∧
      θ1 ∈ Set.Ioo (Real.pi / 2) Real.pi ∧
      2 * Real.cos θ1 = t1 ∧
      θ2 ∈ Set.Ioo (Real.pi / 2) Real.pi ∧
      2 * Real.cos θ2 = t2

/-- Paper label: `cor:sync-kernel-weighted-xi-three-quadratics`. The earlier single-exception-pair
theorem already produces the three real cubic roots together with the two critical-line angle
parameters and the exceptional reciprocal root pair. -/
theorem paper_sync_kernel_weighted_xi_three_quadratics :
    sync_kernel_weighted_xi_three_quadratics_statement := by
  rcases paper_sync_kernel_weighted_xi_exception_coordinate with
    ⟨t1, t2, t3, α, β, θ1, θ2, ht1lo, ht1hi, hPt1, ht2lo, ht2hi, hPt2, ht3lo, ht3hi, hPt3,
      hα, hβ, hαgt1, hsum, hβpos, hpowβ, hpowNeg, hNβ, hNnegβ, hθ1, hcos1, hθ2, hcos2⟩
  have hNα : sync_kernel_weighted_xi_single_exception_pair_N α = 0 := by
    rw [hpowβ] at hNβ
    exact hNβ
  have hNαinv : sync_kernel_weighted_xi_single_exception_pair_N α⁻¹ = 0 := by
    rw [hpowNeg] at hNnegβ
    exact hNnegβ
  refine ⟨t1, t2, t3, α, β, θ1, θ2, ht1lo, ht1hi, hPt1, ht2lo, ht2hi, hPt2, ht3lo, ht3hi,
    hPt3, hα, hβ, hαgt1, ?_, hsum, hNα, hNαinv, hθ1, hcos1, hθ2, hcos2⟩
  · have hαquad := sync_kernel_weighted_xi_single_exception_pair_alpha_quad (by linarith : 2 < t3)
    simpa [hα] using hαquad.2

end Omega.SyncKernelWeighted
