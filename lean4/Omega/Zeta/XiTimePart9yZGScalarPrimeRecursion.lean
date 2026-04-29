import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9y-zg-scalar-prime-recursion`. -/
theorem paper_xi_time_part9y_zg_scalar_prime_recursion
    (p x y r : Nat -> Real)
    (hp : forall n, 1 <= n -> 0 < p n)
    (hx0 : x 0 = 1)
    (hy0 : y 0 = 0)
    (hstep : forall n, 1 <= n ->
      x n = p n / (p n + 1) * (x (n - 1) + y (n - 1)) ∧
        y n = (1 / (p n + 1)) * x (n - 1))
    (hr : forall n, 1 <= n -> r n = y n / x n) :
    r 1 = 1 / p 1 ∧
      (forall n, 1 <= n -> r (n + 1) = 1 / (p (n + 1) * (1 + r n))) := by
  have paper_xi_time_part9y_zg_scalar_prime_recursion_xy_nonneg :
      forall n, 0 <= x n ∧ 0 <= y n := by
    intro n
    induction n with
    | zero =>
        constructor
        · simp [hx0]
        · simp [hy0]
    | succ n ih =>
        have hn : 1 <= n + 1 := by omega
        rcases hstep (n + 1) hn with ⟨hx_step, hy_step⟩
        have hp_pos : 0 < p (n + 1) := hp (n + 1) hn
        have hden_pos : 0 < p (n + 1) + 1 := by linarith
        constructor
        · rw [hx_step]
          exact mul_nonneg (div_nonneg hp_pos.le hden_pos.le) (add_nonneg ih.1 ih.2)
        · rw [hy_step]
          exact mul_nonneg (div_nonneg zero_le_one hden_pos.le) ih.1
  have paper_xi_time_part9y_zg_scalar_prime_recursion_x_pos :
      forall n, 0 < x n := by
    intro n
    induction n with
    | zero =>
        simp [hx0]
    | succ n ih =>
        have hn : 1 <= n + 1 := by omega
        rcases hstep (n + 1) hn with ⟨hx_step, _⟩
        have hp_pos : 0 < p (n + 1) := hp (n + 1) hn
        have hden_pos : 0 < p (n + 1) + 1 := by linarith
        have hsum_pos : 0 < x n + y n :=
          add_pos_of_pos_of_nonneg ih
            (paper_xi_time_part9y_zg_scalar_prime_recursion_xy_nonneg n).2
        rw [hx_step]
        exact mul_pos (div_pos hp_pos hden_pos) hsum_pos
  constructor
  · have hstep1 := hstep 1 (by norm_num)
    have hp1_pos : 0 < p 1 := hp 1 (by norm_num)
    have hden1_pos : 0 < p 1 + 1 := by linarith
    have hx1 : x 1 = p 1 / (p 1 + 1) := by
      rw [hstep1.1, hx0, hy0]
      ring
    have hy1 : y 1 = 1 / (p 1 + 1) := by
      rw [hstep1.2, hx0]
      ring
    calc
      r 1 = y 1 / x 1 := hr 1 (by norm_num)
      _ = (1 / (p 1 + 1)) / (p 1 / (p 1 + 1)) := by rw [hy1, hx1]
      _ = 1 / p 1 := by
        field_simp [ne_of_gt hp1_pos, ne_of_gt hden1_pos]
  · intro n hn
    have hn_next : 1 <= n + 1 := by omega
    rcases hstep (n + 1) hn_next with ⟨hx_step, hy_step⟩
    have hp_next_pos : 0 < p (n + 1) := hp (n + 1) hn_next
    have hden_next_pos : 0 < p (n + 1) + 1 := by linarith
    have hx_n_pos : 0 < x n :=
      paper_xi_time_part9y_zg_scalar_prime_recursion_x_pos n
    have hsum_pos : 0 < x n + y n :=
      add_pos_of_pos_of_nonneg hx_n_pos
        (paper_xi_time_part9y_zg_scalar_prime_recursion_xy_nonneg n).2
    calc
      r (n + 1) = y (n + 1) / x (n + 1) := hr (n + 1) hn_next
      _ =
          ((1 / (p (n + 1) + 1)) * x n) /
            ((p (n + 1) / (p (n + 1) + 1)) * (x n + y n)) := by
        rw [hy_step, hx_step]
        simp
      _ = 1 / (p (n + 1) * (1 + y n / x n)) := by
        field_simp
          [ne_of_gt hp_next_pos, ne_of_gt hden_next_pos, ne_of_gt hx_n_pos,
            ne_of_gt hsum_pos]
      _ = 1 / (p (n + 1) * (1 + r n)) := by
        rw [hr n hn]

end Omega.Zeta
