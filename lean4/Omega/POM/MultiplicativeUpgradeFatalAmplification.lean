import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Omega.POM

/-- The concrete tensor mode obtained by keeping one copy of the non-Perron eigenvector. -/
def pom_multiplicative_upgrade_fatal_amplification_tensor_mode (u v : ℝ) (b : ℕ) : ℝ :=
  u ^ (b - 1) * v

/-- The Perron scale of the `b`-fold multiplicative upgrade. -/
def pom_multiplicative_upgrade_fatal_amplification_upgraded_radius (ρ : ℝ) (b : ℕ) : ℝ :=
  ρ ^ b

/-- The lower envelope coming from one transported non-Perron mode. -/
def pom_multiplicative_upgrade_fatal_amplification_nonperron_lower_bound
    (ρ η : ℝ) (b : ℕ) : ℝ :=
  ρ ^ (b - 1) * η

/-- Paper label: `thm:pom-multiplicative-upgrade-fatal-amplification`.
In the concrete tensor model, the transported mode `u^(b-1) * v` stays nonzero, the induced
non-Perron lower bound scales like `ρ^(b-1) η`, and for `ρ > 1` with `η ≥ 1` that lower bound
already dominates the square-root barrier. -/
theorem paper_pom_multiplicative_upgrade_fatal_amplification
    (u v ρ η : ℝ) (b : ℕ) (hu : u ≠ 0) (hv : v ≠ 0) (hρ : 1 < ρ) (hη : 1 ≤ η) (hb : 2 ≤ b) :
    pom_multiplicative_upgrade_fatal_amplification_tensor_mode u v b ≠ 0 ∧
      pom_multiplicative_upgrade_fatal_amplification_upgraded_radius ρ b = ρ ^ b ∧
      pom_multiplicative_upgrade_fatal_amplification_nonperron_lower_bound ρ η b =
        ρ ^ (b - 1) * η ∧
      ρ ≤ pom_multiplicative_upgrade_fatal_amplification_nonperron_lower_bound ρ η b ∧
      Real.sqrt ρ <
        pom_multiplicative_upgrade_fatal_amplification_nonperron_lower_bound ρ η b := by
  have hρ_nonneg : 0 ≤ ρ := le_trans zero_le_one hρ.le
  have hpow : ρ ≤ ρ ^ (b - 1) := by
    have hpow_aux : 1 ≤ ρ ^ (b - 2) := by
      exact one_le_pow₀ hρ.le
    calc
      ρ = ρ * 1 := by ring
      _ ≤ ρ * ρ ^ (b - 2) := by
        exact mul_le_mul_of_nonneg_left hpow_aux hρ_nonneg
      _ = ρ ^ (b - 1) := by
        rw [show b - 1 = (b - 2) + 1 by omega, pow_add, pow_one]
        ring
  have hpow_nonneg : 0 ≤ ρ ^ (b - 1) := by
    positivity
  have hmul : ρ ^ (b - 1) ≤ ρ ^ (b - 1) * η := by
    have hmul' : ρ ^ (b - 1) * 1 ≤ ρ ^ (b - 1) * η := by
      exact mul_le_mul_of_nonneg_left hη hpow_nonneg
    simpa using hmul'
  have hlower : ρ ≤ pom_multiplicative_upgrade_fatal_amplification_nonperron_lower_bound ρ η b :=
    le_trans hpow hmul
  have hsqrt_lt : Real.sqrt ρ < ρ := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt ρ := Real.sqrt_nonneg ρ
    nlinarith [Real.sq_sqrt hρ_nonneg]
  refine ⟨?_, rfl, rfl, hlower, lt_of_lt_of_le hsqrt_lt hlower⟩
  unfold pom_multiplicative_upgrade_fatal_amplification_tensor_mode
  exact mul_ne_zero (pow_ne_zero (b - 1) hu) hv

end Omega.POM
