import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9y-zg-infinite-product-positivity`. -/
theorem paper_xi_time_part9y_zg_infinite_product_positivity (p r s : ℕ → ℝ)
    (hstep :
      ∀ n, s (n + 1) = s n * (1 - r n / ((p (n + 1) + 1) * (1 + r n))))
    (hs0 : s 0 = 1) (hp : ∀ n, 0 < p (n + 1)) (hr_nonneg : ∀ n, 0 ≤ r n)
    (hr_small : ∀ n, r n ≤ 1 / p (n + 1)) :
    (∀ N,
      s N =
        (Finset.range N).prod fun n => (1 - r n / ((p (n + 1) + 1) * (1 + r n)))) ∧
      ∀ N,
        0 <
          (Finset.range N).prod fun n =>
            (1 - r n / ((p (n + 1) + 1) * (1 + r n))) := by
  constructor
  · intro N
    induction N with
    | zero =>
        simp [hs0]
    | succ N ih =>
        rw [hstep N, ih, Finset.prod_range_succ]
  · intro N
    refine Finset.prod_pos ?_
    intro n _hn
    have _hr_small_n : r n ≤ 1 / p (n + 1) := hr_small n
    let den : ℝ := (p (n + 1) + 1) * (1 + r n)
    have hden_pos : 0 < den := by
      dsimp [den]
      exact mul_pos (by linarith [hp n]) (by linarith [hr_nonneg n])
    have hlt_den : r n < den := by
      dsimp [den]
      nlinarith [hp n, hr_nonneg n]
    have hfrac_lt_one : r n / den < 1 := by
      calc
        r n / den < den / den := div_lt_div_of_pos_right hlt_den hden_pos
        _ = 1 := div_self (ne_of_gt hden_pos)
    dsimp [den] at hfrac_lt_one
    linarith

end Omega.Zeta
