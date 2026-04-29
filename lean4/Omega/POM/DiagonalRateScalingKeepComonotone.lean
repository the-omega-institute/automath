import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-diagonal-rate-scaling-keep-comonotone`. Positive diagonal rate
scaling preserves the common order of the weight, background, and keep-probability profiles. -/
theorem paper_pom_diagonal_rate_scaling_keep_comonotone {X : Type*} [Fintype X]
    (w u π p : X → ℝ) (A κ Z : ℝ)
    (hA : 0 < A) (hκ : 0 < κ) (hZ : 0 < Z) (hu : ∀ x, 0 < u x)
    (hπ : ∀ x, π x = u x / A)
    (hp : ∀ x, p x = (1 + κ) * u x / (A + κ * u x))
    (hmarg : ∀ x, w x = u x * (A + κ * u x) / Z) :
    (∀ x y, w y ≤ w x → u y ≤ u x ∧ π y ≤ π x ∧ p y ≤ p x) := by
  intro x y hw
  have hnum : u y * (A + κ * u y) ≤ u x * (A + κ * u x) := by
    rw [hmarg y, hmarg x] at hw
    exact (div_le_div_iff_of_pos_right hZ).1 hw
  have hu_le : u y ≤ u x := by
    by_contra hnot
    have hxy : u x < u y := lt_of_not_ge hnot
    have hfactor :
        u y * (A + κ * u y) - u x * (A + κ * u x) =
          (u y - u x) * (A + κ * (u y + u x)) := by
      ring
    have hpos_factor : 0 < (u y - u x) * (A + κ * (u y + u x)) := by
      have hleft : 0 < u y - u x := sub_pos.mpr hxy
      have hsum_pos : 0 < u y + u x := add_pos (hu y) (hu x)
      have hκsum_pos : 0 < κ * (u y + u x) := mul_pos hκ hsum_pos
      have hright : 0 < A + κ * (u y + u x) := add_pos hA hκsum_pos
      exact mul_pos hleft hright
    have hstrict : u x * (A + κ * u x) < u y * (A + κ * u y) := by
      nlinarith
    exact (not_lt_of_ge hnum) hstrict
  have hπ_le : π y ≤ π x := by
    rw [hπ y, hπ x]
    exact div_le_div_of_nonneg_right hu_le hA.le
  have hp_le : p y ≤ p x := by
    have hden_y : 0 < A + κ * u y := add_pos hA (mul_pos hκ (hu y))
    have hden_x : 0 < A + κ * u x := add_pos hA (mul_pos hκ (hu x))
    have hcross : u y * (A + κ * u x) ≤ u x * (A + κ * u y) := by
      nlinarith
    have hratio :
        u y / (A + κ * u y) ≤ u x / (A + κ * u x) := by
      rw [div_le_div_iff₀ hden_y hden_x]
      exact hcross
    have honeκ_nonneg : 0 ≤ 1 + κ := by linarith
    rw [hp y, hp x]
    simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left hratio honeκ_nonneg
  exact ⟨hu_le, hπ_le, hp_le⟩

end Omega.POM
