import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Folding

/-- The `μ = -1` specialization of the branch-point equations. -/
def gaugeAnomalyMuMinusOneBranchCondition (t u : ℂ) : Prop :=
  t * u = 2 ∧ u ^ 3 = 1

private theorem real_cube_root_eq_one {u : ℝ} (h : u ^ 3 = 1) : u = 1 := by
  have hzero : u ^ 3 - 1 = 0 := by linarith
  have hfactor : (u - 1) * (u ^ 2 + u + 1) = 0 := by
    calc
      (u - 1) * (u ^ 2 + u + 1) = u ^ 3 - 1 := by ring
      _ = 0 := hzero
  have hpos : 0 < u ^ 2 + u + 1 := by
    have hsquare : 0 ≤ (u + (1 / 2 : ℝ)) ^ 2 := sq_nonneg (u + (1 / 2 : ℝ))
    nlinarith
  have hu : u - 1 = 0 := by
    nlinarith
  linarith

/-- Paper-facing classification of the `μ = -1` branch resonance: in the complex domain the branch
points are indexed by the cube roots of unity, while the real slice collapses to `(t,u) = (2,1)`.
    cor:fold-gauge-anomaly-mu-minus1-branch-classification -/
theorem paper_fold_gauge_anomaly_mu_minus1_branch_classification :
    (∀ t u : ℂ,
      gaugeAnomalyMuMinusOneBranchCondition t u ↔
        ∃ ζ : ℂ, ζ ^ 3 = 1 ∧ t = 2 / ζ ∧ u = ζ) ∧
    ∀ t u : ℝ, t * u = 2 → u ^ 3 = 1 → t = 2 ∧ u = 1 := by
  refine ⟨?_, ?_⟩
  · intro t u
    constructor
    · rintro ⟨htu, hu3⟩
      refine ⟨u, hu3, ?_, rfl⟩
      have hu0 : u ≠ 0 := by
        intro hu0
        rw [hu0] at hu3
        norm_num at hu3
      exact (eq_div_iff hu0).2 (by simpa [mul_comm] using htu)
    · rintro ⟨zeta, hzeta3, ht, hu⟩
      subst t
      subst u
      constructor
      · have hzeta0 : zeta ≠ 0 := by
          intro hzeta0
          rw [hzeta0] at hzeta3
          norm_num at hzeta3
        rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hzeta0, mul_one]
      · exact hzeta3
  · intro t u htu hu3
    have hu : u = 1 := real_cube_root_eq_one hu3
    constructor
    · rw [hu] at htu
      nlinarith
    · exact hu

end Omega.Folding
