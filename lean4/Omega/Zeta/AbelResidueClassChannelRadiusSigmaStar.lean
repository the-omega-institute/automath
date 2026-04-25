import Mathlib.Tactic
import Omega.Zeta.AbelGrowthExponentCriterion

namespace Omega.Zeta

noncomputable section

/-- Residue-class channel radius obtained from the base Cauchy-Hadamard radius by the `k`-fold
power rescaling. The residue index `j` is present only to record the channel label. -/
def abel_residue_class_channel_radius_sigma_star_channel_radius
    (b σ : ℝ) (k _j : ℕ) : ℝ :=
  (abel_growth_exponent_criterion_sigma_radius b σ) ^ k

/-- Paper label: `cor:abel-residue-class-channel-radius-sigma-star`. In this seed model the
residue-class radius is independent of the residue label `j`, equals the `k`-th power of the base
radius, and the rightmost real part is read off from the logarithm of that radius. -/
theorem paper_abel_residue_class_channel_radius_sigma_star
    (b σ : ℝ) (k j₁ j₂ : ℕ) (hb : 1 < b) (hk : 1 ≤ k) :
    abel_residue_class_channel_radius_sigma_star_channel_radius b σ k j₁ =
      abel_residue_class_channel_radius_sigma_star_channel_radius b σ k j₂ ∧
      abel_residue_class_channel_radius_sigma_star_channel_radius b σ k j₁ =
        Real.exp (-((k : ℝ) * (σ - 1 / 2) * Real.log b)) ∧
      σ =
        1 / 2 -
          Real.log (abel_residue_class_channel_radius_sigma_star_channel_radius b σ k j₁) /
            ((k : ℝ) * Real.log b) := by
  have hbase_pos : 0 < abel_growth_exponent_criterion_sigma_radius b σ := by
    unfold abel_growth_exponent_criterion_sigma_radius
    positivity
  have hformula :
      abel_residue_class_channel_radius_sigma_star_channel_radius b σ k j₁ =
        Real.exp (-((k : ℝ) * (σ - 1 / 2) * Real.log b)) := by
    unfold abel_residue_class_channel_radius_sigma_star_channel_radius
      abel_growth_exponent_criterion_sigma_radius
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hk0 : (k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le (by decide : 0 < 1) hk)
  have hb0 : 0 < b := lt_trans zero_lt_one hb
  have hlogb : Real.log b ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hb0 (ne_of_gt hb)
  have hlog :
      Real.log (abel_residue_class_channel_radius_sigma_star_channel_radius b σ k j₁) =
        -((k : ℝ) * (σ - 1 / 2) * Real.log b) := by
    rw [hformula, Real.log_exp]
  have hdiv :
      Real.log (abel_residue_class_channel_radius_sigma_star_channel_radius b σ k j₁) /
          ((k : ℝ) * Real.log b) =
        -(σ - 1 / 2) := by
    apply (div_eq_iff (mul_ne_zero hk0 hlogb)).2
    calc
      Real.log (abel_residue_class_channel_radius_sigma_star_channel_radius b σ k j₁) =
          -((k : ℝ) * (σ - 1 / 2) * Real.log b) := hlog
      _ = (-(σ - 1 / 2)) * ((k : ℝ) * Real.log b) := by ring
  refine ⟨by rfl, hformula, ?_⟩
  calc
    σ = 1 / 2 - (-(σ - 1 / 2)) := by ring
    _ =
        1 / 2 -
          Real.log (abel_residue_class_channel_radius_sigma_star_channel_radius b σ k j₁) /
            ((k : ℝ) * Real.log b) := by rw [hdiv]

end

end Omega.Zeta
