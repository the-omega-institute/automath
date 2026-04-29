import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-collision-square-root-normalization-trichotomy`. Once the slow mode is
written as `ratio u ^ n`, the critical value is constant, the subcritical bound is immediate from
that identity, and the supercritical chamber grows past one after at least one step. -/
theorem paper_xi_collision_square_root_normalization_trichotomy (ratio : ℝ → ℝ)
    (S : ℕ → ℝ → ℝ) (uR : ℝ) (hS : ∀ n u, S n u = ratio u ^ n)
    (hsub : ∀ u, 0 < u → u < uR → ratio u < 1) (hcrit : ratio uR = 1)
    (hsuper : ∀ u, uR < u → 1 < ratio u) :
    (∀ n, S n uR = 1) ∧
      (∀ u n, 0 < u → u < uR → S n u ≤ ratio u ^ n) ∧
        (∀ u n, uR < u → 1 < S (n + 1) u) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    simp [hS, hcrit]
  · intro u n hu_pos hu_lt
    have _hratio_lt_one : ratio u < 1 := hsub u hu_pos hu_lt
    simp [hS]
  · intro u n hu
    rw [hS]
    exact one_lt_pow₀ (hsuper u hu) (Nat.succ_ne_zero n)

end Omega.Zeta
