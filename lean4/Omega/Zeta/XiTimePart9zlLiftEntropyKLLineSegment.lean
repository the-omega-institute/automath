import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9zl-lift-entropy-kl-line-segment`. -/
theorem paper_xi_time_part9zl_lift_entropy_kl_line_segment {Lift : Type*}
    (H D : Lift → ℝ) (Hmin Hmax : ℝ) (ledger : ∀ μ, D μ = Hmax - H μ)
    (entropy_bounds : ∀ μ, Hmin ≤ H μ ∧ H μ ≤ Hmax)
    (entropy_surj : ∀ h, Hmin ≤ h → h ≤ Hmax → ∃ μ, H μ = h) :
    {p : ℝ × ℝ | ∃ μ, p = (H μ, D μ)} =
      {p : ℝ × ℝ | ∃ h, Hmin ≤ h ∧ h ≤ Hmax ∧ p = (h, Hmax - h)} := by
  ext p
  constructor
  · rintro ⟨μ, rfl⟩
    rcases entropy_bounds μ with ⟨hmin, hmax⟩
    exact ⟨H μ, hmin, hmax, by simp [ledger μ]⟩
  · rintro ⟨h, hmin, hmax, hp⟩
    rcases entropy_surj h hmin hmax with ⟨μ, hμ⟩
    refine ⟨μ, ?_⟩
    rw [hp]
    ext <;> simp [hμ, ledger μ]

end Omega.Zeta
