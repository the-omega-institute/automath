import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9zj-zero-density-no-bounded-closure-collision-scale`. -/
theorem paper_xi_time_part9zj_zero_density_no_bounded_closure_collision_scale
    (η Cscale : ℕ → ℝ) (sixWindow : ℕ → Prop)
    (hη_nonneg : ∀ m, sixWindow m → 0 ≤ η m)
    (hη_zero : ∀ δ : ℝ, 0 < δ → ∃ N, ∀ m, N ≤ m → sixWindow m → η m < δ)
    (hC_unbounded : ∀ B N0, ∃ m, N0 ≤ m ∧ sixWindow m ∧ B ≤ Cscale m) :
    ¬ ∃ Ψ : ℝ → ℝ,
      (∃ δ C : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 ≤ x → x < δ → Ψ x ≤ C) ∧
        ∃ N, ∀ m, N ≤ m → sixWindow m → Cscale m ≤ Ψ (η m) := by
  rintro ⟨Ψ, ⟨δ, C, hδ_pos, hΨ_bounded⟩, ⟨NΨ, heventual⟩⟩
  rcases hη_zero δ hδ_pos with ⟨Nη, hη_small⟩
  rcases hC_unbounded (C + 1) (max NΨ Nη) with ⟨m, hm_max, hm_window, hC_large⟩
  have hm_NΨ : NΨ ≤ m := le_trans (Nat.le_max_left NΨ Nη) hm_max
  have hm_Nη : Nη ≤ m := le_trans (Nat.le_max_right NΨ Nη) hm_max
  have hη_lt : η m < δ := hη_small m hm_Nη hm_window
  have hη_nonneg_m : 0 ≤ η m := hη_nonneg m hm_window
  have hCscale_le : Cscale m ≤ Ψ (η m) := heventual m hm_NΨ hm_window
  have hΨ_le : Ψ (η m) ≤ C := hΨ_bounded (η m) hη_nonneg_m hη_lt
  linarith

end Omega.Zeta
