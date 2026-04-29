import Omega.Zeta.XiProjectiveMomentRadiusSubmultiplicative

namespace Omega.Zeta

noncomputable section

/-- Integer-degenerate moment-kernel radius, identified with the projective radius proxy. -/
def xi_time_part9r_moment_kernel_radius (q : ℕ) : ℝ :=
  xi_projective_moment_radius_submultiplicative_radius q

/-- Paper label: `thm:xi-time-part9r-moment-kernel-radius-submultiplicative`. -/
theorem paper_xi_time_part9r_moment_kernel_radius_submultiplicative {r : ℕ → ℝ}
    (hpos : ∀ q, 2 ≤ q → 0 < r q)
    (hdegenerate : ∀ q, 2 ≤ q → r q = xi_time_part9r_moment_kernel_radius q) (a b : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) : r (a + b) ≤ r a * r b := by
  have _ := hpos
  have hab : 2 ≤ a + b := le_trans ha (Nat.le_add_right a b)
  rw [hdegenerate (a + b) hab, hdegenerate a ha, hdegenerate b hb]
  exact paper_xi_projective_moment_radius_submultiplicative ha hb

end

end Omega.Zeta
