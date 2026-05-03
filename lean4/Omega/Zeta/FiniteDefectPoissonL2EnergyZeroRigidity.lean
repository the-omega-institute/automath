import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-finite-defect-poisson-l2-energy-zero-rigidity`. -/
theorem paper_xi_finite_defect_poisson_l2_energy_zero_rigidity (m δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) :
    Real.pi * m^2 * (δ^2 / (1 - δ^2)) = 0 ↔ m = 0 ∨ δ = 0 := by
  have hδsq_le : δ ^ 2 ≤ δ := by
    have hδle1 : δ ≤ 1 := le_of_lt hδ1
    calc δ ^ 2 = δ * δ := by ring
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left hδle1 hδ0
      _ = δ := by ring
  have hden_pos : 0 < 1 - δ ^ 2 := by nlinarith
  have hden_ne : 1 - δ ^ 2 ≠ 0 := ne_of_gt hden_pos
  constructor
  · intro h
    have hpi_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have hprod : m ^ 2 * (δ ^ 2 / (1 - δ ^ 2)) = 0 := by
      have h' : Real.pi * (m ^ 2 * (δ ^ 2 / (1 - δ ^ 2))) = 0 := by
        simpa [mul_assoc] using h
      exact (mul_eq_zero.mp h').resolve_left hpi_ne
    rcases mul_eq_zero.mp hprod with hm2 | hfrac
    · exact Or.inl (sq_eq_zero_iff.mp hm2)
    · right
      have hδ2 : δ ^ 2 = 0 := (div_eq_zero_iff.mp hfrac).resolve_right hden_ne
      exact sq_eq_zero_iff.mp hδ2
  · rintro (hm | hδ)
    · simp [hm]
    · simp [hδ]

end Omega.Zeta
