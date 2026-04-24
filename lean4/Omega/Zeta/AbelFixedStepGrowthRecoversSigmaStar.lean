import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Omega.Zeta.AbelResidueClassChannelRadiusSigmaStar

namespace Omega.Zeta

noncomputable section

/-- The fixed-step limsup growth rate predicted by the residue-class radius formula. -/
def xi_abel_fixed_step_growth_recovers_sigma_star_growth_rate
    (m : ℕ) (b σ : ℝ) : ℝ :=
  (m : ℝ) * (σ - 1 / 2) * Real.log b

/-- Paper label: `cor:xi-abel-fixed-step-growth-recovers-sigma-star`.
For every fixed step `m`, the power-rescaled radius formula yields the exact exponential growth
rate and recovers `σ` by solving the resulting logarithmic identity. -/
theorem paper_xi_abel_fixed_step_growth_recovers_sigma_star (m : ℕ) (b : ℝ) :
    1 ≤ m → 1 < b →
      ∀ σ : ℝ,
        let Λ := xi_abel_fixed_step_growth_recovers_sigma_star_growth_rate m b σ
        Λ =
            Real.log
              (1 /
                abel_residue_class_channel_radius_sigma_star_channel_radius b σ m 0) ∧
          σ = 1 / 2 + Λ / ((m : ℝ) * Real.log b) := by
  intro hm hb σ
  dsimp [xi_abel_fixed_step_growth_recovers_sigma_star_growth_rate]
  have hm0 : (m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le (by decide : 0 < 1) hm)
  have hlogb : Real.log b ≠ 0 := by
    exact Real.log_ne_zero_of_pos_of_ne_one (lt_trans zero_lt_one hb) (ne_of_gt hb)
  have hradius :
      abel_residue_class_channel_radius_sigma_star_channel_radius b σ m 0 =
        Real.exp (-((m : ℝ) * (σ - 1 / 2) * Real.log b)) := by
    have hpack :=
      (paper_abel_residue_class_channel_radius_sigma_star b σ m 0 0 hb hm).2.1
    simpa using hpack
  refine ⟨?_, ?_⟩
  · rw [hradius]
    have hexp_ne : Real.exp (-((m : ℝ) * (σ - 1 / 2) * Real.log b)) ≠ 0 :=
      (Real.exp_pos _).ne'
    symm
    calc
      Real.log (1 / Real.exp (-((m : ℝ) * (σ - 1 / 2) * Real.log b))) =
          Real.log ((Real.exp (-((m : ℝ) * (σ - 1 / 2) * Real.log b)))⁻¹) := by
            rw [one_div]
      _ = -Real.log (Real.exp (-((m : ℝ) * (σ - 1 / 2) * Real.log b))) := by
            rw [Real.log_inv]
      _ = (m : ℝ) * (σ - 1 / 2) * Real.log b := by
            rw [Real.log_exp]
            ring
  · field_simp [hm0, hlogb]
    ring

end

end Omega.Zeta
