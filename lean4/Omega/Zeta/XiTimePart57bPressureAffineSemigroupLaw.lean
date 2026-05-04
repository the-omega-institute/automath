import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part57b-pressure-affine-semigroup-law`. -/
theorem paper_xi_time_part57b_pressure_affine_semigroup_law
    (P : ℕ → ℝ) (ac a b : ℕ) (alpha g : ℝ)
    (hfreeze : ∀ t : ℕ, ac < t → P t = (t : ℝ) * alpha + g)
    (ha : ac < a) (hb : ac < b) :
    P a = (a : ℝ) * alpha + g ∧
      P (a + 1) - P a = alpha ∧
      P (a + b) = P a + P b - g := by
  have hPa : P a = (a : ℝ) * alpha + g := hfreeze a ha
  have hPb : P b = (b : ℝ) * alpha + g := hfreeze b hb
  have hPa1 : P (a + 1) = ((a + 1 : ℕ) : ℝ) * alpha + g := by
    exact hfreeze (a + 1) (by omega)
  have hPab : P (a + b) = ((a + b : ℕ) : ℝ) * alpha + g := by
    exact hfreeze (a + b) (by omega)
  refine ⟨hPa, ?_, ?_⟩
  · rw [hPa1, hPa]
    norm_num
    ring
  · rw [hPab, hPa, hPb]
    norm_num
    ring

end Omega.Zeta
