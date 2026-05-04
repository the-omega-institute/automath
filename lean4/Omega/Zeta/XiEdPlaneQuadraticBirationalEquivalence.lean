import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-ed-plane-quadratic-birational-equivalence`. -/
theorem paper_xi_ed_plane_quadratic_birational_equivalence (m y u : ℚ)
    (hA : (m - 2) * (m + 2)^2 ≠ 0)
    (hu : u = 2 * ((m - 2) * (m + 2)^2) * y + (4 * m^2 - 17)) :
    (((m - 2) * (m + 2)^2) * y^2 + (4 * m^2 - 17) * y + (4 * m - 7) = 0 ↔
      u^2 = -4 * m^3 - 16 * m^2 + 16 * m + 65) := by
  subst u
  let A : ℚ := (m - 2) * (m + 2)^2
  have hA' : A ≠ 0 := by
    simpa [A] using hA
  have h4A : 4 * A ≠ 0 := by
    exact mul_ne_zero (by norm_num : (4 : ℚ) ≠ 0) hA'
  have hid :
      (2 * A * y + (4 * m^2 - 17))^2 - (-4 * m^3 - 16 * m^2 + 16 * m + 65) =
        4 * A * (A * y^2 + (4 * m^2 - 17) * y + (4 * m - 7)) := by
    dsimp [A]
    ring
  change
    (A * y^2 + (4 * m^2 - 17) * y + (4 * m - 7) = 0 ↔
      (2 * A * y + (4 * m^2 - 17))^2 = -4 * m^3 - 16 * m^2 + 16 * m + 65)
  constructor
  · intro hF
    have hzero :
        (2 * A * y + (4 * m^2 - 17))^2 -
            (-4 * m^3 - 16 * m^2 + 16 * m + 65) = 0 := by
      rw [hid, hF]
      ring
    nlinarith
  · intro hE
    have hzero : 4 * A * (A * y^2 + (4 * m^2 - 17) * y + (4 * m - 7)) = 0 := by
      rw [← hid]
      nlinarith
    exact (mul_eq_zero.mp hzero).resolve_left h4A

end Omega.Zeta
