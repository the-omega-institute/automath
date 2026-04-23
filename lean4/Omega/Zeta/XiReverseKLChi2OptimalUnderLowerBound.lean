import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Endpoint constant appearing in the reverse-KL versus `χ²` comparison. -/
noncomputable def xi_reversekl_chi2_optimal_under_lower_bound_kappa (a : ℝ) : ℝ :=
  (a - 1 - Real.log a) / (a - 1) ^ (2 : ℕ)

lemma xi_reversekl_chi2_optimal_under_lower_bound_log_ge_one_sub_inv (x : ℝ) (hx : 0 < x) :
    1 - 1 / x ≤ Real.log x := by
  have hInv : Real.log (x⁻¹) ≤ x⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  have hInv' : -Real.log x ≤ x⁻¹ - 1 := by simpa [Real.log_inv] using hInv
  have hInv'' : 1 - x⁻¹ ≤ Real.log x := by linarith
  simpa [one_div] using hInv''

lemma xi_reversekl_chi2_optimal_under_lower_bound_endpoint {a : ℝ} (ha1 : a ≠ 1) :
    a - 1 - Real.log a =
      xi_reversekl_chi2_optimal_under_lower_bound_kappa a * (a - 1) ^ (2 : ℕ) := by
  unfold xi_reversekl_chi2_optimal_under_lower_bound_kappa
  have ha10 : a - 1 ≠ 0 := sub_ne_zero.mpr ha1
  field_simp [ha10]

/-- Paper label: `thm:xi-reversekl-chi2-optimal-under-lower-bound`. For `0 < a < 1`, the scalar
reverse-KL defect `x - 1 - log x` admits the elementary quadratic upper bound
`(1 / a) * (x - 1)^2` on `[a, ∞)`, while the endpoint value `x = a` identifies the exact constant
`κ(a) = (a - 1 - log a)/(a - 1)^2` that every admissible quadratic coefficient must dominate. -/
theorem paper_xi_reversekl_chi2_optimal_under_lower_bound :
    ∀ a : ℝ, 0 < a → a < 1 →
      let κ := xi_reversekl_chi2_optimal_under_lower_bound_kappa a
      (∀ x : ℝ, a ≤ x → x - 1 - Real.log x ≤ (1 / a) * (x - 1) ^ (2 : ℕ)) ∧
        (a - 1 - Real.log a = κ * (a - 1) ^ (2 : ℕ)) ∧
        (∀ C : ℝ, (∀ x : ℝ, a ≤ x → x - 1 - Real.log x ≤ C * (x - 1) ^ (2 : ℕ)) → κ ≤ C) := by
  intro a ha0 ha1
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · intro x hax
    have hx0 : 0 < x := lt_of_lt_of_le ha0 hax
    have hlog : 1 - 1 / x ≤ Real.log x :=
      xi_reversekl_chi2_optimal_under_lower_bound_log_ge_one_sub_inv x hx0
    have hmain : x - 1 - Real.log x ≤ (x - 1) ^ (2 : ℕ) / x := by
      have hxne : x ≠ 0 := ne_of_gt hx0
      have hrew : x - 1 - (1 - 1 / x) = (x - 1) ^ (2 : ℕ) / x := by
        field_simp [hxne]
      calc
        x - 1 - Real.log x ≤ x - 1 - (1 - 1 / x) := by linarith
        _ = (x - 1) ^ (2 : ℕ) / x := hrew
    have hxa : 1 / x ≤ 1 / a := one_div_le_one_div_of_le ha0 hax
    have hsq_nonneg : 0 ≤ (x - 1) ^ (2 : ℕ) := by positivity
    calc
      x - 1 - Real.log x ≤ (x - 1) ^ (2 : ℕ) / x := hmain
      _ ≤ (x - 1) ^ (2 : ℕ) / a := by
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
          mul_le_mul_of_nonneg_left hxa hsq_nonneg
      _ = (1 / a) * (x - 1) ^ (2 : ℕ) := by ring
  · exact xi_reversekl_chi2_optimal_under_lower_bound_endpoint ha1.ne
  · intro C hC
    have hAtA : a - 1 - Real.log a ≤ C * (a - 1) ^ (2 : ℕ) := hC a le_rfl
    have hsq_nonneg : 0 ≤ (a - 1) ^ (2 : ℕ) := by positivity
    have hsq_ne : (a - 1) ^ (2 : ℕ) ≠ 0 := by
      exact pow_ne_zero 2 (sub_ne_zero.mpr ha1.ne)
    have hsq_pos : 0 < (a - 1) ^ (2 : ℕ) := lt_of_le_of_ne hsq_nonneg (Ne.symm hsq_ne)
    have hEq :
        a - 1 - Real.log a =
          xi_reversekl_chi2_optimal_under_lower_bound_kappa a * (a - 1) ^ (2 : ℕ) :=
      xi_reversekl_chi2_optimal_under_lower_bound_endpoint ha1.ne
    rw [hEq] at hAtA
    nlinarith

end Omega.Zeta
