import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part62dcb-zg-density-second-order-summability`. -/
theorem paper_xi_time_part62dcb_zg_density_second_order_summability (p r : ℕ → ℝ)
    (hp : ∀ n ≥ 1, 1 < p n) (hr0 : r 0 = 1)
    (hr : ∀ n ≥ 1, r n = p n / (p n + r (n - 1))) (hr_pos : ∀ n, 0 < r n)
    (hsum : Summable (fun n : ℕ => 1 / (p (n + 1) * (p (n + 2) + 1)))) :
    (∀ n ≥ 1, 0 < 1 - r n ∧ 1 - r n ≤ 1 / p n) ∧
      (∀ n ≥ 2,
        0 < 1 - (p n + r (n - 1)) / (p n + 1) ∧
          1 - (p n + r (n - 1)) / (p n + 1) ≤
            1 / (p (n - 1) * (p n + 1))) ∧
        Summable
          (fun n : ℕ => |1 - (p (n + 2) + r (n + 1)) / (p (n + 2) + 1)|) := by
  have hp_pos : ∀ n, 1 ≤ n → 0 < p n := by
    intro n hn
    linarith [hp n hn]
  have hp_add_pos : ∀ n, 1 ≤ n → 0 < p n + 1 := by
    intro n hn
    linarith [hp n hn]
  have hmain : ∀ n ≥ 1, 0 < 1 - r n ∧ 1 - r n ≤ 1 / p n := by
    intro n hn
    induction n using Nat.strong_induction_on with
    | h n ih =>
        have hp_n : 0 < p n := hp_pos n hn
        have hr_prev_pos : 0 < r (n - 1) := hr_pos (n - 1)
        have hden_pos : 0 < p n + r (n - 1) := by linarith
        have hden_ne : p n + r (n - 1) ≠ 0 := hden_pos.ne'
        have hdef_eq : 1 - r n = r (n - 1) / (p n + r (n - 1)) := by
          rw [hr n hn]
          field_simp [hden_ne]
          ring
        constructor
        · rw [hdef_eq]
          positivity
        · rw [hdef_eq]
          have hr_prev_le_one : r (n - 1) ≤ 1 := by
            by_cases hbase : n = 1
            · subst n
              simp [hr0]
            · have hprev_ge : 1 ≤ n - 1 := by omega
              have hprev_lt : n - 1 < n := by omega
              have hprev_pos := (ih (n - 1) hprev_lt hprev_ge).1
              linarith
          rw [div_le_div_iff₀ hden_pos hp_n]
          nlinarith [mul_le_mul_of_nonneg_left hr_prev_le_one (le_of_lt hp_n)]
  have hsecond : ∀ n ≥ 2,
      0 < 1 - (p n + r (n - 1)) / (p n + 1) ∧
        1 - (p n + r (n - 1)) / (p n + 1) ≤
          1 / (p (n - 1) * (p n + 1)) := by
    intro n hn
    have hn1 : 1 ≤ n := by omega
    have hprev_ge : 1 ≤ n - 1 := by omega
    have hp_n_add_pos : 0 < p n + 1 := hp_add_pos n hn1
    have hp_n_add_ne : p n + 1 ≠ 0 := hp_n_add_pos.ne'
    have hp_prev_pos : 0 < p (n - 1) := hp_pos (n - 1) hprev_ge
    have hprev := hmain (n - 1) hprev_ge
    have hdef_eq :
        1 - (p n + r (n - 1)) / (p n + 1) = (1 - r (n - 1)) / (p n + 1) := by
      field_simp [hp_n_add_ne]
      ring
    constructor
    · rw [hdef_eq]
      exact div_pos hprev.1 hp_n_add_pos
    · rw [hdef_eq]
      calc
        (1 - r (n - 1)) / (p n + 1) ≤ (1 / p (n - 1)) / (p n + 1) := by
          exact div_le_div_of_nonneg_right hprev.2 (le_of_lt hp_n_add_pos)
        _ = 1 / (p (n - 1) * (p n + 1)) := by
          field_simp [hp_prev_pos.ne', hp_n_add_pos.ne']
  refine ⟨hmain, hsecond, ?_⟩
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) ?_ hsum
  intro n
  have hn2 : 2 ≤ n + 2 := by omega
  have hbound := (hsecond (n + 2) hn2).2
  have hpos := (hsecond (n + 2) hn2).1
  have habs :
      |1 - (p (n + 2) + r (n + 1)) / (p (n + 2) + 1)| =
        1 - (p (n + 2) + r (n + 1)) / (p (n + 2) + 1) := by
    exact abs_of_pos hpos
  simpa [habs, Nat.add_sub_cancel] using hbound

end Omega.Zeta
