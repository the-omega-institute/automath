import Mathlib

namespace Omega.POM

theorem paper_pom_diagonal_rate_refresh_hitting_time_rank_two_potential {α : Type}
    [Fintype α] [DecidableEq α] (m : α → α → ℝ) (A B Φ : α → ℝ) :
    (∀ x y, x ≠ y → m x y = A x + B y) →
      (∀ x, Φ x = A x - B x) →
        (∀ x y, x ≠ y → m x y - m y x = Φ x - Φ y) := by
  intro hm hΦ x y hxy
  rw [hm x y hxy, hm y x hxy.symm, hΦ x, hΦ y]
  ring

end Omega.POM
