import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-fold-zero-density-no-bounded-control-on-normalized-collision`. -/
theorem paper_xi_fold_zero_density_no_bounded_control_on_normalized_collision
    (δ Γ : ℕ → ℝ) (c : ℝ) (hδ_nonneg : ∀ n, 0 ≤ δ n)
    (hδ_zero : ∀ ε > 0, ∃ N, ∀ n ≥ N, δ n < ε) (hc : 0 < c)
    (hΓ_lower : ∃ N, ∀ n ≥ N, c ≤ Γ n) :
    ¬ ∃ η : ℝ → ℝ,
      (∀ ε > 0, ∃ ρ > 0, ∀ t, 0 ≤ t → t < ρ → η t < ε) ∧
        (∃ N, ∀ n ≥ N, Γ n ≤ η (δ n)) := by
  rintro ⟨η, hη_small, hΓ_control⟩
  rcases hη_small (c / 2) (by linarith) with ⟨ρ, hρ_pos, hηρ⟩
  rcases hδ_zero ρ hρ_pos with ⟨Nδ, hδρ⟩
  rcases hΓ_lower with ⟨Nlower, hlower⟩
  rcases hΓ_control with ⟨Ncontrol, hcontrol⟩
  let n := max Nδ (max Nlower Ncontrol)
  have hnδ : n ≥ Nδ := by
    exact Nat.le_max_left _ _
  have hnlower : n ≥ Nlower := by
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hncontrol : n ≥ Ncontrol := by
    exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hη_lt : η (δ n) < c / 2 := hηρ (δ n) (hδ_nonneg n) (hδρ n hnδ)
  have hchain : c ≤ η (δ n) := (hlower n hnlower).trans (hcontrol n hncontrol)
  linarith

end Omega.Zeta
