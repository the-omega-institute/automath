import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

namespace Omega.Zeta

/-- The endpoint radial parameter `ρ = 1 - η`. -/
noncomputable def xi_endpoint_angle_height_exchange_rho (η : ℝ) : ℝ :=
  1 - η

/-- The endpoint angular parameter `θ = π - ε`. -/
noncomputable def xi_endpoint_angle_height_exchange_theta (ε : ℝ) : ℝ :=
  Real.pi - ε

/-- The closed-form endpoint transfer law. -/
noncomputable def xi_endpoint_angle_height_exchange_transfer (η ε : ℝ) : ℝ :=
  let ρ := xi_endpoint_angle_height_exchange_rho η
  let θ := xi_endpoint_angle_height_exchange_theta ε
  (1 - ρ ^ 2) / (1 + ρ ^ 2 + 2 * ρ * Real.cos θ)

private lemma xi_endpoint_angle_height_exchange_closed_form (η ε : ℝ) :
    xi_endpoint_angle_height_exchange_transfer η ε =
      (2 * η - η ^ 2) / (η ^ 2 + 2 * (1 - η) * (1 - Real.cos ε)) := by
  simp [xi_endpoint_angle_height_exchange_transfer, xi_endpoint_angle_height_exchange_rho,
    xi_endpoint_angle_height_exchange_theta, Real.cos_pi_sub]
  ring_nf

/-- Paper label: `thm:xi-endpoint-angle-height-exchange`. Expanding the endpoint closed form at
`ρ = 1 - η` and `θ = π - ε` isolates the denominator as `η²` plus an angular correction bounded by
`ε²`, which yields the lower endpoint window bound `η / (η² + ε²)`. -/
theorem paper_xi_endpoint_angle_height_exchange {η ε : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    xi_endpoint_angle_height_exchange_transfer η ε =
      (2 * η - η ^ 2) / (η ^ 2 + 2 * (1 - η) * (1 - Real.cos ε)) ∧
      η ^ 2 + 2 * (1 - η) * (1 - Real.cos ε) ≤ η ^ 2 + ε ^ 2 ∧
      η / (η ^ 2 + ε ^ 2) ≤ xi_endpoint_angle_height_exchange_transfer η ε := by
  have hform := xi_endpoint_angle_height_exchange_closed_form η ε
  have hcos : 1 - Real.cos ε ≤ ε ^ 2 / 2 := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := ε)]
  have hone_minus_eta : 0 ≤ 1 - η := by linarith
  have hden_nonneg : 0 ≤ η ^ 2 + 2 * (1 - η) * (1 - Real.cos ε) := by
    have hcos_nonneg : 0 ≤ 1 - Real.cos ε := by
      linarith [Real.cos_le_one ε]
    nlinarith
  have hden_le :
      η ^ 2 + 2 * (1 - η) * (1 - Real.cos ε) ≤ η ^ 2 + ε ^ 2 := by
    nlinarith
  have hnum_ge : η ≤ 2 * η - η ^ 2 := by
    nlinarith
  refine ⟨hform, hden_le, ?_⟩
  by_cases hηeq : η = 0
  · subst hηeq
    simp [xi_endpoint_angle_height_exchange_closed_form]
  · have hηpos : 0 < η := lt_of_le_of_ne hη0 (by simpa [eq_comm] using hηeq)
    have hterm_nonneg : 0 ≤ 2 * (1 - η) * (1 - Real.cos ε) := by
      have hcos_nonneg : 0 ≤ 1 - Real.cos ε := by
        linarith [Real.cos_le_one ε]
      nlinarith
    have hden_ge_sq : η ^ 2 ≤ η ^ 2 + 2 * (1 - η) * (1 - Real.cos ε) := by
      linarith
    have hden_pos : 0 < η ^ 2 + 2 * (1 - η) * (1 - Real.cos ε) := by
      have hsq : 0 < η ^ 2 := by positivity
      exact lt_of_lt_of_le hsq hden_ge_sq
    have hrecip :
        1 / (η ^ 2 + ε ^ 2) ≤ 1 / (η ^ 2 + 2 * (1 - η) * (1 - Real.cos ε)) := by
      exact one_div_le_one_div_of_le hden_pos hden_le
    have hleft :
        η / (η ^ 2 + ε ^ 2) ≤ η / (η ^ 2 + 2 * (1 - η) * (1 - Real.cos ε)) := by
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hrecip hη0
    have hright :
        η / (η ^ 2 + 2 * (1 - η) * (1 - Real.cos ε)) ≤
          (2 * η - η ^ 2) / (η ^ 2 + 2 * (1 - η) * (1 - Real.cos ε)) := by
      exact div_le_div_of_nonneg_right hnum_ge hden_pos.le
    calc
      η / (η ^ 2 + ε ^ 2) ≤ η / (η ^ 2 + 2 * (1 - η) * (1 - Real.cos ε)) := hleft
      _ ≤ (2 * η - η ^ 2) / (η ^ 2 + 2 * (1 - η) * (1 - Real.cos ε)) := hright
      _ = xi_endpoint_angle_height_exchange_transfer η ε := by simpa [hform] using hform.symm

end Omega.Zeta
