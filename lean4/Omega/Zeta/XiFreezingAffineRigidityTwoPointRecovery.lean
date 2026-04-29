import Mathlib.Tactic

theorem paper_xi_freezing_affine_rigidity_two_point_recovery
    (P : Nat -> Real) (alpha g ac : Real)
    (hfrozen : ∀ q : Nat, 1 ≤ q -> ac < (q : Real) -> P q = (q : Real) * alpha + g)
    (a b : Nat) (ha : 1 ≤ a) (hab : a < b) (hac : ac < (a : Real)) :
    alpha = (P b - P a) / ((b : Real) - (a : Real)) ∧
      g = ((b : Real) * P a - (a : Real) * P b) / ((b : Real) - (a : Real)) ∧
      (∀ q : Nat, 1 ≤ q -> ac < (q : Real) -> alpha = P (q + 1) - P q) ∧
      (∀ q : Nat, 2 ≤ q -> ac < ((q - 1 : Nat) : Real) ->
        P (q + 1) - 2 * P q + P (q - 1) = 0) := by
  have hb : 1 ≤ b := by omega
  have habReal : (a : Real) < (b : Real) := by exact_mod_cast hab
  have hbc : ac < (b : Real) := by linarith
  have hden : (b : Real) - (a : Real) ≠ 0 := by linarith
  have haP := hfrozen a ha hac
  have hbP := hfrozen b hb hbc
  constructor
  · rw [haP, hbP]
    field_simp [hden]
    ring
  constructor
  · rw [haP, hbP]
    field_simp [hden]
    ring
  constructor
  · intro q hq hqc
    have hq1 : 1 ≤ q + 1 := by omega
    have hq_lt_q1 : (q : Real) < ((q + 1 : Nat) : Real) := by
      exact_mod_cast Nat.lt_succ_self q
    have hqc1 : ac < ((q + 1 : Nat) : Real) := by linarith
    have hqP := hfrozen q hq hqc
    have hq1P := hfrozen (q + 1) hq1 hqc1
    rw [hqP, hq1P]
    norm_num
    ring
  · intro q hq hqcprev
    have hqm1 : 1 ≤ q - 1 := by omega
    have hqpos : 1 ≤ q := by omega
    have hq1 : 1 ≤ q + 1 := by omega
    have hqm1_lt_q_nat : q - 1 < q := by omega
    have hq_lt_q1_nat : q < q + 1 := Nat.lt_succ_self q
    have hqm1_lt_q : ((q - 1 : Nat) : Real) < (q : Real) := by
      exact_mod_cast hqm1_lt_q_nat
    have hq_lt_q1 : (q : Real) < ((q + 1 : Nat) : Real) := by
      exact_mod_cast hq_lt_q1_nat
    have hqc : ac < (q : Real) := by linarith
    have hqc1 : ac < ((q + 1 : Nat) : Real) := by linarith
    have hqm1P := hfrozen (q - 1) hqm1 hqcprev
    have hqP := hfrozen q hqpos hqc
    have hq1P := hfrozen (q + 1) hq1 hqc1
    have hcast_m1 : ((q - 1 : Nat) : Real) = (q : Real) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ q)]
      norm_num
    have hcast_p1 : ((q + 1 : Nat) : Real) = (q : Real) + 1 := by norm_num
    rw [hqm1P, hqP, hq1P, hcast_m1, hcast_p1]
    ring
