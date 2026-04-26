import Mathlib.Tactic
import Mathlib.Topology.Algebra.Order.Field

namespace Omega.Zeta

open Filter

/-- Paper label: `cor:xi-bounded-flux-forces-kappa0`. -/
theorem paper_xi_bounded_flux_forces_kappa0
    (m : ℕ) (hm : 1 < m) (κ : ℝ) (hκ : 0 ≤ κ)
    (hbounded : ∃ C : ℝ, ∀ n : ℕ, |((m : ℝ) ^ n) * κ| ≤ C) :
    κ = 0 := by
  by_contra hκ_ne_zero
  have hκ_pos : 0 < κ := by
    exact lt_of_le_of_ne hκ (Ne.symm hκ_ne_zero)
  rcases hbounded with ⟨C, hC⟩
  have hm_real : 1 < (m : ℝ) := by exact_mod_cast hm
  have hpow : Tendsto (fun n : ℕ => (m : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hm_real
  have hscaled : Tendsto (fun n : ℕ => κ * (m : ℝ) ^ n) atTop atTop :=
    Tendsto.const_mul_atTop hκ_pos hpow
  have hscaled' : Tendsto (fun n : ℕ => ((m : ℝ) ^ n) * κ) atTop atTop := by
    simpa [mul_comm] using hscaled
  have heventually : ∀ᶠ n : ℕ in atTop, C < ((m : ℝ) ^ n) * κ :=
    hscaled'.eventually (eventually_gt_atTop C)
  rcases eventually_atTop.mp heventually with ⟨N, hN⟩
  have hgt : C < ((m : ℝ) ^ N) * κ := hN N le_rfl
  have hle_abs : ((m : ℝ) ^ N) * κ ≤ |((m : ℝ) ^ N) * κ| := le_abs_self _
  have hle_bound : |((m : ℝ) ^ N) * κ| ≤ C := hC N
  linarith

end Omega.Zeta
