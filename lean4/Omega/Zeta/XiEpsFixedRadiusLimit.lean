import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

open scoped Topology

namespace Omega.Zeta

/-- Concrete fixed-epsilon radius-limit package: the map `ρ ↦ ρ * exp (-ε)` tends to
`exp (-ε)` as `ρ → 1`, is monotone in `ρ`, and the limiting window scale is the reciprocal
hyperbolic sine expression. -/
def xi_eps_fixed_radius_limit_statement : Prop :=
  ∀ ε ρ ρ' : ℝ,
    0 < ε →
      Filter.Tendsto (fun ϱ : ℝ => ϱ * Real.exp (-ε)) (𝓝 (1 : ℝ))
          (𝓝 (Real.exp (-ε))) ∧
        (ρ ≤ ρ' → ρ * Real.exp (-ε) ≤ ρ' * Real.exp (-ε)) ∧
          2 * Real.exp (-ε) / (1 - Real.exp (-2 * ε)) = (Real.sinh ε)⁻¹

/-- Paper label: `cor:xi-eps-fixed-radius-limit`. The fixed-epsilon radius map has the stated
limit and monotonicity, and its limiting scale simplifies to `1 / sinh ε`. -/
theorem paper_xi_eps_fixed_radius_limit : xi_eps_fixed_radius_limit_statement := by
  intro ε ρ ρ' hε
  have hlim :
      Filter.Tendsto (fun ϱ : ℝ => ϱ * Real.exp (-ε)) (𝓝 (1 : ℝ))
        (𝓝 ((1 : ℝ) * Real.exp (-ε))) := by
    exact (continuousAt_id.mul continuousAt_const).tendsto
  have hmono : ρ ≤ ρ' → ρ * Real.exp (-ε) ≤ ρ' * Real.exp (-ε) := by
    intro hρ
    exact mul_le_mul_of_nonneg_right hρ (le_of_lt (Real.exp_pos _))
  have hden_sinh : Real.exp ε - Real.exp (-ε) ≠ 0 := by
    have hlt : Real.exp (-ε) < Real.exp ε := Real.exp_lt_exp.mpr (by linarith)
    exact sub_ne_zero.mpr hlt.ne'
  have hden_exp : 1 - Real.exp (-2 * ε) ≠ 0 := by
    have hlt : Real.exp (-2 * ε) < 1 := by
      simpa using (Real.exp_lt_one_iff.mpr (by linarith : -2 * ε < 0))
    exact sub_ne_zero.mpr hlt.ne'
  have hid :
      2 * Real.exp (-ε) / (1 - Real.exp (-2 * ε)) = (Real.sinh ε)⁻¹ := by
    rw [Real.sinh_eq]
    have hfactor :
        1 - Real.exp (-2 * ε) =
          (Real.exp ε - Real.exp (-ε)) * Real.exp (-ε) := by
      have hmul_one : Real.exp ε * Real.exp (-ε) = 1 := by
        rw [← Real.exp_add]
        ring_nf
        simp
      have hsquare : Real.exp (-ε) * Real.exp (-ε) = Real.exp (-2 * ε) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        1 - Real.exp (-2 * ε)
            = Real.exp ε * Real.exp (-ε) - Real.exp (-ε) * Real.exp (-ε) := by
              rw [hmul_one, hsquare]
        _ = (Real.exp ε - Real.exp (-ε)) * Real.exp (-ε) := by ring
    rw [hfactor]
    field_simp [hden_sinh, Real.exp_ne_zero]
  exact ⟨by simpa using hlim, hmono, hid⟩

end Omega.Zeta
