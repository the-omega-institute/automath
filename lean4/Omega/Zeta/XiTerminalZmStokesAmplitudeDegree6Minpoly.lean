import Omega.Zeta.XiTerminalZmStokesAmplitudeSquareCubicRigidity

namespace Omega.Zeta

/-- Paper label: `thm:xi-terminal-zm-stokes-amplitude-degree6-minpoly`. -/
theorem paper_xi_terminal_zm_stokes_amplitude_degree6_minpoly :
    (∀ q : ℚ, (162 : ℚ) * q ^ 6 + 1593 * q ^ 4 + 1998 * q ^ 2 + 1184 ≠ 0) ∧
      (∀ b t : ℚ, t = b ^ 2 →
        (162 : ℚ) * t ^ 3 + 1593 * t ^ 2 + 1998 * t + 1184 = 0 → False) := by
  refine ⟨?_, ?_⟩
  · intro q hq
    exact xi_terminal_zm_stokes_amplitude_square_cubic_rigidity_no_rational_root (q ^ 2) (by
      ring_nf at hq ⊢
      exact hq)
  · intro b t ht ht_root
    subst ht
    exact xi_terminal_zm_stokes_amplitude_square_cubic_rigidity_no_rational_root (b ^ 2) (by
      ring_nf at ht_root ⊢
      exact ht_root)

end Omega.Zeta
