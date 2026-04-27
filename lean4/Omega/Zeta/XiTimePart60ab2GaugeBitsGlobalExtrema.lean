import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Zeta.XiAuditedEvenGaugeEntropyBalancedLowerBound

namespace Omega.Zeta

open scoped BigOperators

private lemma xi_time_part60ab2_gauge_bits_global_extrema_two_factorial_le
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Nat.factorial a * Nat.factorial b ≤ Nat.factorial (a + b - 1) := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha) with ⟨a', rfl⟩
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb) with ⟨b', rfl⟩
  have hbase : b' + 1 ≤ Nat.choose (a' + 1 + b') b' := by
    have hle : b' + 1 ≤ a' + 1 + b' := by omega
    have hmono := Nat.choose_le_choose (c := b') hle
    simpa [Nat.choose_succ_self_right] using hmono
  have hmul :
      (b' + 1) * (Nat.factorial (a' + 1) * Nat.factorial b') ≤
        Nat.choose (a' + 1 + b') b' * (Nat.factorial (a' + 1) * Nat.factorial b') :=
    Nat.mul_le_mul_right _ hbase
  calc
    Nat.factorial (a' + 1) * Nat.factorial (b' + 1) =
        (b' + 1) * (Nat.factorial (a' + 1) * Nat.factorial b') := by
      rw [show Nat.factorial (b' + 1) = (b' + 1) * Nat.factorial b' by
        exact Nat.factorial_succ b']
      ring_nf
    _ ≤ Nat.choose (a' + 1 + b') b' *
        (Nat.factorial (a' + 1) * Nat.factorial b') := hmul
    _ = Nat.factorial (a' + 1 + b') := by
      rw [← Nat.add_choose_mul_factorial_mul_factorial (a' + 1) b']
      ring_nf
    _ = Nat.factorial ((a' + 1) + (b' + 1) - 1) := by
      congr 1

private lemma xi_time_part60ab2_gauge_bits_global_extrema_prod_factorial_le_aux
    (n : ℕ) (d : Fin (n + 1) → ℕ) (hpos : ∀ i, 0 < d i) :
    (∏ i, Nat.factorial (d i)) ≤ Nat.factorial ((∑ i, d i) - (n + 1) + 1) := by
  induction n with
  | zero =>
      have hge : 1 ≤ d 0 := Nat.succ_le_of_lt (hpos 0)
      simp [Nat.sub_add_cancel hge]
  | succ n ih =>
      let tail : Fin (n + 1) → ℕ := fun i => d i.succ
      have htail_pos : ∀ i, 0 < tail i := fun i => hpos i.succ
      have htail := ih tail htail_pos
      have htail_sum_ge : n + 1 ≤ ∑ i, tail i := by
        calc
          n + 1 = ∑ _i : Fin (n + 1), 1 := by simp
          _ ≤ ∑ i : Fin (n + 1), tail i := by
            exact Finset.sum_le_sum fun i _ => htail_pos i
      have htail_arg_pos : 0 < (∑ i, tail i) - (n + 1) + 1 := by
        omega
      have hmerge :
          Nat.factorial (d 0) * Nat.factorial ((∑ i, tail i) - (n + 1) + 1) ≤
            Nat.factorial (d 0 + ((∑ i, tail i) - (n + 1) + 1) - 1) :=
        xi_time_part60ab2_gauge_bits_global_extrema_two_factorial_le
          (d 0) ((∑ i, tail i) - (n + 1) + 1) (hpos 0) htail_arg_pos
      calc
        ∏ i : Fin (n + 2), Nat.factorial (d i) =
            Nat.factorial (d 0) * ∏ i : Fin (n + 1), Nat.factorial (tail i) := by
          rw [Fin.prod_univ_succ]
        _ ≤ Nat.factorial (d 0) * Nat.factorial ((∑ i, tail i) - (n + 1) + 1) := by
          exact Nat.mul_le_mul_left _ htail
        _ ≤ Nat.factorial (d 0 + ((∑ i, tail i) - (n + 1) + 1) - 1) := hmerge
        _ = Nat.factorial ((∑ i : Fin (n + 2), d i) - (n + 2) + 1) := by
          have hsum_tail :
              (∑ i : Fin (n + 2), d i) = d 0 + ∑ i : Fin (n + 1), tail i := by
            rw [Fin.sum_univ_succ]
          have hidx :
              d 0 + ((∑ i : Fin (n + 1), tail i) - (n + 1) + 1) - 1 =
                (∑ i : Fin (n + 2), d i) - (n + 2) + 1 := by
            clear htail hmerge
            have hd0pos : 0 < d 0 := hpos 0
            have htailge : n + 1 ≤ ∑ i, tail i := htail_sum_ge
            rw [hsum_tail]
            omega
          exact congrArg Nat.factorial hidx

private lemma xi_time_part60ab2_gauge_bits_global_extrema_prod_factorial_le
    {L N : ℕ} (hL : 0 < L) (d : Fin L → ℕ) (hpos : ∀ i, 0 < d i)
    (hsum : (∑ i, d i) = N) :
    (∏ i, Nat.factorial (d i)) ≤ Nat.factorial (N - L + 1) := by
  cases L with
  | zero => omega
  | succ n =>
      simpa [hsum] using
        xi_time_part60ab2_gauge_bits_global_extrema_prod_factorial_le_aux n d hpos

private lemma xi_time_part60ab2_gauge_bits_global_extrema_sum_log_factorial_eq_log_prod
    {L : ℕ} (d : Fin L → ℕ) :
    (∑ i, Real.log (Nat.factorial (d i))) =
      Real.log ((∏ i, (Nat.factorial (d i) : ℝ))) := by
  rw [Real.log_prod]
  intro i _
  exact_mod_cast Nat.factorial_ne_zero (d i)

/-- Paper label: `thm:xi-time-part60ab2-gauge-bits-global-extrema`. -/
theorem paper_xi_time_part60ab2_gauge_bits_global_extrema (N L q r : ℕ) (hL : 0 < L)
    (hN : L ≤ N) (hdiv : N = q * L + r) (hr : r < L) :
    (∀ d : Fin L → ℕ, (∀ i, 0 < d i) → (∑ i, d i) = N →
        (L - r : ℝ) * Real.log (Nat.factorial q) +
            (r : ℝ) * Real.log (Nat.factorial (q + 1)) ≤
          ∑ i, Real.log (Nat.factorial (d i))) ∧
      (∀ d : Fin L → ℕ, (∀ i, 0 < d i) → (∑ i, d i) = N →
        (∑ i, Real.log (Nat.factorial (d i))) ≤
          Real.log (Nat.factorial (N - L + 1))) := by
  have _ : L ≤ N := hN
  constructor
  · intro d hpos hsum
    have hrle : r ≤ L := Nat.le_of_lt hr
    have hbalanced : (∑ i, d i) = (L - r) * q + r * (q + 1) := by
      rw [hsum, hdiv, Nat.mul_succ]
      rw [show q * L = (L - r) * q + r * q by
        conv_lhs => rw [← Nat.sub_add_cancel hrle]
        rw [Nat.mul_add, Nat.mul_comm q (L - r), Nat.mul_comm q r]]
      ring
    exact paper_xi_audited_even_gauge_entropy_balanced_lower_bound L q r d hrle
      (fun i => Nat.succ_le_of_lt (hpos i)) hbalanced
  · intro d hpos hsum
    have hprod_le :=
      xi_time_part60ab2_gauge_bits_global_extrema_prod_factorial_le hL d hpos hsum
    have hlog_le :
        Real.log ((∏ i, (Nat.factorial (d i) : ℝ))) ≤
          Real.log (Nat.factorial (N - L + 1) : ℝ) := by
      exact Real.log_le_log (by positivity) (by exact_mod_cast hprod_le)
    calc
      (∑ i, Real.log (Nat.factorial (d i))) =
          Real.log ((∏ i, (Nat.factorial (d i) : ℝ))) :=
        xi_time_part60ab2_gauge_bits_global_extrema_sum_log_factorial_eq_log_prod d
      _ ≤ Real.log (Nat.factorial (N - L + 1) : ℝ) := hlog_le

end Omega.Zeta
