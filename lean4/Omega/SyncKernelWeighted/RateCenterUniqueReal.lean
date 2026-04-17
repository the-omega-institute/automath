import Mathlib.Tactic
import Omega.SyncKernelWeighted.RateCurveCenterSliceAudit

namespace Omega.SyncKernelWeighted

/-- The audited center slice `R(1/2, u) = -((u - 1)^6 * Q(u)) / 64` has the unique real zero
`u = 1`, and the residual factor is nonzero there. This records the exact multiplicity-six
certificate used in the paper. -/
theorem paper_rate_center_unique_real :
    (∀ u : ℝ, (-((u - 1)^6) * rateCenterQReal u / (64 : ℝ) = 0) ↔ u = 1) ∧
      rateCenterQReal 1 ≠ 0 := by
  rcases paper_rate_center_q_reciprocal_no_real with ⟨_, hNoRoots, _⟩
  refine ⟨?_, hNoRoots 1⟩
  intro u
  constructor
  · intro h
    have hnum : -((u - 1) ^ 6) * rateCenterQReal u = 0 := by
      field_simp at h
      simpa using h
    have hq : rateCenterQReal u ≠ 0 := hNoRoots u
    have hpow : (u - 1) ^ 6 = 0 := by
      have hneg : -((u - 1) ^ 6) = 0 := (mul_eq_zero.mp hnum).resolve_right hq
      linarith
    have hu1 : u - 1 = 0 := eq_zero_of_pow_eq_zero hpow
    linarith
  · intro hu
    subst hu
    simp

end Omega.SyncKernelWeighted
