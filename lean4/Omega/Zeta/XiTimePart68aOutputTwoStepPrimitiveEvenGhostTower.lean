import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part68a-output-two-step-primitive-even-ghost-tower`. -/
theorem paper_xi_time_part68a_output_two_step_primitive_even_ghost_tower
    (u : ℝ)
    (a : ℕ → ℝ)
    (hevenCoeff : ∀ m, 1 ≤ m → a (2 * m) / (2 * m : ℝ) = 8 * u ^ m / (m : ℝ))
    (hoddCoeff : ∀ m, a (2 * m + 1) = 0) :
    (∀ m, 1 ≤ m → a (2 * m) = 16 * u ^ m) ∧
      (∀ m, a (2 * m + 1) = 0) := by
  refine ⟨?_, hoddCoeff⟩
  intro m hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mp hm)
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have h2mne : (2 * m : ℝ) ≠ 0 := by positivity
  have hcoeff := hevenCoeff m hm
  calc
    a (2 * m) = (a (2 * m) / (2 * m : ℝ)) * (2 * m : ℝ) := by
      exact (div_mul_cancel₀ (a (2 * m)) h2mne).symm
    _ = (8 * u ^ m / (m : ℝ)) * (2 * m : ℝ) := by rw [hcoeff]
    _ = 16 * u ^ m := by
      field_simp [hmne]
      ring

end Omega.Zeta
