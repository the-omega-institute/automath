import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-gx-local-sign-flip-falsifier`. -/
theorem paper_xi_gx_local_sign_flip_falsifier {g : ℝ → ℝ} {u0 m C eps0 : ℝ}
    (hm : 0 < m) (hC : 0 ≤ C) (heps0 : 0 < eps0)
    (hbound :
      ∀ u, |u - u0| < eps0 → u ≠ u0 → |g u - (2 * m) / (u - u0)| ≤ C) :
    ∃ eps > 0,
      (∀ u, u0 - eps < u → u < u0 → g u < 0) ∧
        (∀ u, u0 < u → u < u0 + eps → 0 < g u) := by
  let eps := min eps0 (m / (C + 1))
  have hC1_pos : 0 < C + 1 := by linarith
  have heps_pos : 0 < eps := by
    exact lt_min heps0 (div_pos hm hC1_pos)
  refine ⟨eps, heps_pos, ?_, ?_⟩
  · intro u hleft hright
    let t : ℝ := u0 - u
    have ht_pos : 0 < t := by dsimp [t]; linarith
    have ht_lt_eps : t < eps := by dsimp [t, eps] at hleft ⊢; linarith
    have hdist : |u - u0| < eps0 := by
      rw [abs_of_neg]
      · linarith [ht_lt_eps, min_le_left eps0 (m / (C + 1))]
      · linarith
    have hne : u ≠ u0 := by linarith
    have hb := hbound u hdist hne
    have hupper : g u - (2 * m) / (u - u0) ≤ C := (abs_le.mp hb).2
    have ht_lt_ratio : t < m / (C + 1) := lt_of_lt_of_le ht_lt_eps (min_le_right _ _)
    have ht_mul_lt : t * (C + 1) < m := (lt_div_iff₀ hC1_pos).mp ht_lt_ratio
    have hCt_lt : C * t < 2 * m := by
      nlinarith [ht_mul_lt, mul_nonneg hC (le_of_lt ht_pos), hm]
    have hC_lt : C < (2 * m) / t := (lt_div_iff₀ ht_pos).mpr hCt_lt
    have hpole :
        (2 * m) / (u - u0) = -((2 * m) / t) := by
      have ht_ne : t ≠ 0 := ne_of_gt ht_pos
      have hden : u - u0 = -t := by dsimp [t]; ring
      rw [hden]
      field_simp [ht_ne]
    have hprincipal : (2 * m) / (u - u0) + C < 0 := by
      rw [hpole]
      linarith
    linarith
  · intro u hleft hright
    let t : ℝ := u - u0
    have ht_pos : 0 < t := by dsimp [t]; linarith
    have ht_lt_eps : t < eps := by dsimp [t, eps] at hright ⊢; linarith
    have hdist : |u - u0| < eps0 := by
      rw [abs_of_pos ht_pos]
      exact lt_of_lt_of_le ht_lt_eps (min_le_left _ _)
    have hne : u ≠ u0 := by linarith
    have hb := hbound u hdist hne
    have hlower : -C ≤ g u - (2 * m) / (u - u0) := (abs_le.mp hb).1
    have ht_lt_ratio : t < m / (C + 1) := lt_of_lt_of_le ht_lt_eps (min_le_right _ _)
    have ht_mul_lt : t * (C + 1) < m := (lt_div_iff₀ hC1_pos).mp ht_lt_ratio
    have hCt_lt : C * t < 2 * m := by
      nlinarith [ht_mul_lt, mul_nonneg hC (le_of_lt ht_pos), hm]
    have hC_lt : C < (2 * m) / t := (lt_div_iff₀ ht_pos).mpr hCt_lt
    have hprincipal : 0 < (2 * m) / (u - u0) - C := by
      dsimp [t] at hC_lt
      linarith
    linarith

end Omega.Zeta
