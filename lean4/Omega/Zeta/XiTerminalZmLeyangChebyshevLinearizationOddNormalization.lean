import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label:
`prop:xi-terminal-zm-leyang-chebyshev-linearization-odd-normalization`. -/
theorem paper_xi_terminal_zm_leyang_chebyshev_linearization_odd_normalization
    (y r : ℝ) (hr : r * r = 7) (hden : 2 * y + 1 ≠ 0) :
    let psi : ℝ → ℝ := fun s => s ^ 3 - 3 * s
    let a : ℝ :=
      (16 + 69 * y + 219 * y ^ 2 + 128 * y ^ 3) / (8 * (1 + 2 * y) ^ 3)
    let mu : ℝ := r * (5 - 8 * y) / (7 * (2 * y + 1))
    let nu : ℝ → ℝ := fun u => (288 * r / 49) * u - (556 * r / 49)
    nu a = psi mu := by
  dsimp
  rw [show 1 + 2 * y = 2 * y + 1 by ring]
  rw [← sub_eq_zero]
  have hfactor :
      (288 * r / 49 *
              ((16 + 69 * y + 219 * y ^ 2 + 128 * y ^ 3) /
                (8 * (2 * y + 1) ^ 3)) -
            556 * r / 49) -
          ((r * (5 - 8 * y) / (7 * (2 * y + 1))) ^ 3 -
            3 * (r * (5 - 8 * y) / (7 * (2 * y + 1)))) =
        r * (r * r - 7) * (8 * y - 5) ^ 3 / (343 * (2 * y + 1) ^ 3) := by
    have hpoly : 1 + y * 6 + y ^ 2 * 12 + y ^ 3 * 8 ≠ 0 := by
      have h3 : (2 * y + 1) ^ 3 ≠ 0 := pow_ne_zero 3 hden
      ring_nf at h3
      exact h3
    field_simp [hden, hpoly]
    ring_nf
    field_simp [hpoly]
    ring_nf
  rw [hfactor, hr]
  ring

end Omega.Zeta
