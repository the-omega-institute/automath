import Mathlib

namespace Omega.Zeta

/-- The log-radius coordinate used by the Jensen defect interpolation. -/
noncomputable def xi_jensen_logradius_convex_fusion_logRadius (r : ℝ) : ℝ :=
  Real.log r

/-- Concrete log-radius convex fusion statement: a convex defect bound at two radii interpolates
to the intermediate log-radius, and exponentiation preserves the resulting inequality. -/
noncomputable def xi_jensen_logradius_convex_fusion_statement : Prop :=
  ∀ (defect : ℝ → ℝ) (r0 r1 r θ B0 B1 : ℝ),
    0 ≤ θ →
    θ ≤ 1 →
    0 < r0 →
    0 < r1 →
    0 < r →
    xi_jensen_logradius_convex_fusion_logRadius r =
      (1 - θ) * xi_jensen_logradius_convex_fusion_logRadius r0 +
        θ * xi_jensen_logradius_convex_fusion_logRadius r1 →
    defect (xi_jensen_logradius_convex_fusion_logRadius r) ≤
      (1 - θ) * defect (xi_jensen_logradius_convex_fusion_logRadius r0) +
        θ * defect (xi_jensen_logradius_convex_fusion_logRadius r1) →
    defect (xi_jensen_logradius_convex_fusion_logRadius r0) ≤ B0 →
    defect (xi_jensen_logradius_convex_fusion_logRadius r1) ≤ B1 →
      defect (xi_jensen_logradius_convex_fusion_logRadius r) ≤
          (1 - θ) * B0 + θ * B1 ∧
        Real.exp (defect (xi_jensen_logradius_convex_fusion_logRadius r)) ≤
          Real.exp ((1 - θ) * B0 + θ * B1)

theorem paper_xi_jensen_logradius_convex_fusion :
    xi_jensen_logradius_convex_fusion_statement := by
  intro defect r0 r1 r θ B0 B1 hθ0 hθ1 _hr0 _hr1 _hr hlog hconv hB0 hB1
  have hθ0' : 0 ≤ 1 - θ := by linarith
  have hbound :
      defect (xi_jensen_logradius_convex_fusion_logRadius r) ≤
        (1 - θ) * B0 + θ * B1 := by
    nlinarith [hconv, mul_le_mul_of_nonneg_left hB0 hθ0',
      mul_le_mul_of_nonneg_left hB1 hθ0]
  exact ⟨hbound, Real.exp_le_exp.mpr hbound⟩

end Omega.Zeta
