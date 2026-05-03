import Mathlib.Tactic
import Omega.Zeta.XiJoukowskyModsquareArcsineFixedwidth

namespace Omega.Zeta

noncomputable section

/-- The nonnegative Joukowsky branch solves `L + L⁻¹ = c` on `L ≥ 1`. -/
lemma xi_joukowsky_modsquare_quantile_inversion_solve_joukowsky_radius
    (L : ℝ) (hL : 1 ≤ L) :
    L = (L + L⁻¹ + Real.sqrt ((L + L⁻¹) ^ 2 - 4)) / 2 := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hLsq : 1 ≤ L ^ 2 := by
    nlinarith [sq_nonneg (L - 1)]
  have hmul_eq : L * (L - L⁻¹) = L ^ 2 - 1 := by
    field_simp [hLne]
  have hmul_nonneg : 0 ≤ L * (L - L⁻¹) := by
    rw [hmul_eq]
    linarith
  have hdiff_nonneg : 0 ≤ L - L⁻¹ :=
    (mul_nonneg_iff_of_pos_left hLpos).mp hmul_nonneg
  have hsquare : (L + L⁻¹) ^ 2 - 4 = (L - L⁻¹) ^ 2 := by
    field_simp [hLne]
    ring
  have hsqrt : Real.sqrt ((L + L⁻¹) ^ 2 - 4) = L - L⁻¹ := by
    rw [hsquare, Real.sqrt_sq_eq_abs, abs_of_nonneg hdiff_nonneg]
  rw [hsqrt]
  field_simp [hLne]
  ring

/-- Paper label: `prop:xi-joukowsky-modsquare-quantile-inversion`. -/
theorem paper_xi_joukowsky_modsquare_quantile_inversion
    (L α qα : ℝ) (hL : 1 ≤ L) (hα0 : 0 < α) (hα1 : α < 1)
    (hquantile : qα = L + L⁻¹ - 2 * Real.cos (Real.pi * α)) :
    qα = L + L⁻¹ - 2 * Real.cos (Real.pi * α) ∧
      (let c : ℝ := qα + 2 * Real.cos (Real.pi * α)
       L = (c + Real.sqrt (c ^ 2 - 4)) / 2) := by
  have _ : 0 < α := hα0
  have _ : α < 1 := hα1
  refine ⟨hquantile, ?_⟩
  dsimp
  have hc : qα + 2 * Real.cos (Real.pi * α) = L + L⁻¹ := by
    rw [hquantile]
    ring
  rw [hc]
  exact xi_joukowsky_modsquare_quantile_inversion_solve_joukowsky_radius L hL

end

end Omega.Zeta
