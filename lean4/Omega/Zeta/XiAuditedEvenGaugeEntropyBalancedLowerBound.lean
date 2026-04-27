import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

private lemma xi_audited_even_gauge_entropy_balanced_lower_bound_factorial_le_mul_pow_of_le
    {n q : ℕ} (hnq : n ≤ q) :
    q.factorial ≤ n.factorial * (q + 1) ^ (q - n) := by
  induction q generalizing n with
  | zero =>
      have hn : n = 0 := by omega
      simp [hn]
  | succ q ih =>
      by_cases hn : n = q + 1
      · subst n
        simp
      · have hnq' : n ≤ q := by omega
        have hbase := ih hnq'
        calc
          (q + 1).factorial = (q + 1) * q.factorial := by
            rw [Nat.factorial_succ]
          _ ≤ (q + 1) * (n.factorial * (q + 1) ^ (q - n)) := by
            exact Nat.mul_le_mul_left _ hbase
          _ = n.factorial * (q + 1) ^ ((q + 1) - n) := by
            have hsucc : (q + 1) - n = (q - n) + 1 := by omega
            rw [hsucc, pow_succ]
            ring
          _ ≤ n.factorial * (q + 2) ^ ((q + 1) - n) := by
            exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

private lemma xi_audited_even_gauge_entropy_balanced_lower_bound_log_factorial_support
    (q n : ℕ) :
    Real.log (q.factorial) + ((n : ℝ) - (q : ℝ)) * Real.log (q + 1) ≤
      Real.log (n.factorial) := by
  by_cases hqn : q ≤ n
  · have hnat :
        q.factorial * (q + 1) ^ (n - q) ≤ n.factorial := by
      simpa [Nat.add_sub_cancel' hqn] using
        (Nat.factorial_mul_pow_le_factorial (m := q) (n := n - q))
    have hlog :
        Real.log ((q.factorial * (q + 1) ^ (n - q) : ℕ) : ℝ) ≤
          Real.log (n.factorial : ℝ) := by
      exact Real.log_le_log (by positivity) (by exact_mod_cast hnat)
    have hrewrite :
        Real.log ((q.factorial * (q + 1) ^ (n - q) : ℕ) : ℝ) =
          Real.log (q.factorial) + ((n : ℝ) - (q : ℝ)) * Real.log (q + 1) := by
      rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul (by positivity) (by positivity),
        Real.log_pow]
      have hcast : ((n - q : ℕ) : ℝ) = (n : ℝ) - (q : ℝ) := by
        exact Nat.cast_sub hqn
      rw [hcast]
      norm_num [Nat.cast_add, Nat.cast_one]
    calc
      Real.log (q.factorial) + ((n : ℝ) - (q : ℝ)) * Real.log (q + 1) =
          Real.log ((q.factorial * (q + 1) ^ (n - q) : ℕ) : ℝ) := hrewrite.symm
      _ ≤ Real.log (n.factorial) := hlog
  · have hnq : n ≤ q := Nat.le_of_lt (Nat.lt_of_not_ge hqn)
    have hnat :
        q.factorial ≤ n.factorial * (q + 1) ^ (q - n) :=
      xi_audited_even_gauge_entropy_balanced_lower_bound_factorial_le_mul_pow_of_le hnq
    have hlog :
        Real.log (q.factorial : ℝ) ≤
          Real.log ((n.factorial * (q + 1) ^ (q - n) : ℕ) : ℝ) := by
      exact Real.log_le_log (by positivity) (by exact_mod_cast hnat)
    have hrewrite :
        Real.log ((n.factorial * (q + 1) ^ (q - n) : ℕ) : ℝ) =
          Real.log (n.factorial) + ((q : ℝ) - (n : ℝ)) * Real.log (q + 1) := by
      rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul (by positivity) (by positivity),
        Real.log_pow]
      have hcast : ((q - n : ℕ) : ℝ) = (q : ℝ) - (n : ℝ) := by
        exact Nat.cast_sub hnq
      rw [hcast]
      norm_num [Nat.cast_add, Nat.cast_one]
    have hlog' :
        Real.log (q.factorial) ≤
          Real.log (n.factorial) + ((q : ℝ) - (n : ℝ)) * Real.log (q + 1) := by
      calc
        Real.log (q.factorial) ≤
            Real.log ((n.factorial * (q + 1) ^ (q - n) : ℕ) : ℝ) := hlog
        _ = Real.log (n.factorial) + ((q : ℝ) - (n : ℝ)) * Real.log (q + 1) :=
            hrewrite
    linarith

private lemma xi_audited_even_gauge_entropy_balanced_lower_bound_log_factorial_succ
    (q : ℕ) :
    Real.log ((q + 1).factorial) = Real.log (q.factorial) + Real.log (q + 1) := by
  rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
  norm_num [Nat.cast_add, Nat.cast_one]
  ring_nf

/-- Paper label: `thm:xi-audited-even-gauge-entropy-balanced-lower-bound`. The balanced
`q`/`q+1` occupancy profile minimizes the sum of log-factorials among positive integer profiles
with the same total mass. -/
theorem paper_xi_audited_even_gauge_entropy_balanced_lower_bound (r q s : ℕ) (e : Fin r → ℕ)
    (hs : s ≤ r) (hpos : ∀ i, 1 ≤ e i)
    (hsum : (∑ i, e i) = (r - s) * q + s * (q + 1)) :
    (r - s : ℝ) * Real.log (Nat.factorial q) +
        (s : ℝ) * Real.log (Nat.factorial (q + 1)) ≤
      ∑ i, Real.log (Nat.factorial (e i)) := by
  have hpoint :
      ∀ i : Fin r,
        Real.log (q.factorial) + ((e i : ℝ) - (q : ℝ)) * Real.log (q + 1) ≤
          Real.log ((e i).factorial) := by
    intro i
    have _ : 1 ≤ e i := hpos i
    exact xi_audited_even_gauge_entropy_balanced_lower_bound_log_factorial_support q (e i)
  have hsum_point :
      ∑ i : Fin r,
          (Real.log (q.factorial) + ((e i : ℝ) - (q : ℝ)) * Real.log (q + 1)) ≤
        ∑ i : Fin r, Real.log ((e i).factorial) := by
    exact Finset.sum_le_sum fun i _ => hpoint i
  have hsum_simplified : (∑ i : Fin r, e i) = r * q + s := by
    calc
      (∑ i : Fin r, e i) = (r - s) * q + s * (q + 1) := hsum
      _ = r * q + s := by
        rw [Nat.mul_succ]
        have hrs : r - s + s = r := Nat.sub_add_cancel hs
        calc
          (r - s) * q + (s * q + s) = ((r - s) * q + s * q) + s := by ring
          _ = ((r - s + s) * q) + s := by rw [Nat.add_mul]
          _ = r * q + s := by rw [hrs]
  have hleft_sum :
      ∑ i : Fin r,
          (Real.log (q.factorial) + ((e i : ℝ) - (q : ℝ)) * Real.log (q + 1)) =
        (r : ℝ) * Real.log (q.factorial) + (s : ℝ) * Real.log (q + 1) := by
    have hsum_linear :
        ∑ i : Fin r, ((e i : ℝ) - (q : ℝ)) * Real.log (q + 1) =
          (((∑ i : Fin r, e i : ℕ) : ℝ) - (r : ℝ) * (q : ℝ)) * Real.log (q + 1) := by
      calc
        ∑ i : Fin r, ((e i : ℝ) - (q : ℝ)) * Real.log (q + 1) =
            ∑ i : Fin r,
              ((e i : ℝ) * Real.log (q + 1) - (q : ℝ) * Real.log (q + 1)) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              ring
        _ =
            (∑ i : Fin r, (e i : ℝ) * Real.log (q + 1)) -
              ∑ i : Fin r, (q : ℝ) * Real.log (q + 1) := by
              rw [Finset.sum_sub_distrib]
        _ =
            (∑ i : Fin r, (e i : ℝ)) * Real.log (q + 1) -
              (r : ℝ) * ((q : ℝ) * Real.log (q + 1)) := by
              simp [Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
        _ =
            (((∑ i : Fin r, e i : ℕ) : ℝ) - (r : ℝ) * (q : ℝ)) *
              Real.log (q + 1) := by
              rw [Nat.cast_sum]
              ring
    calc
      ∑ i : Fin r,
          (Real.log (q.factorial) + ((e i : ℝ) - (q : ℝ)) * Real.log (q + 1)) =
          (r : ℝ) * Real.log (q.factorial) +
            (((∑ i : Fin r, e i : ℕ) : ℝ) - (r : ℝ) * (q : ℝ)) *
              Real.log (q + 1) := by
            rw [Finset.sum_add_distrib, hsum_linear]
            simp [Finset.sum_const, nsmul_eq_mul]
      _ = (r : ℝ) * Real.log (q.factorial) + (s : ℝ) * Real.log (q + 1) := by
            rw [hsum_simplified]
            norm_num [Nat.cast_add, Nat.cast_mul]
  have htarget :
      (r - s : ℝ) * Real.log (Nat.factorial q) +
          (s : ℝ) * Real.log (Nat.factorial (q + 1)) =
        (r : ℝ) * Real.log (q.factorial) + (s : ℝ) * Real.log (q + 1) := by
    rw [xi_audited_even_gauge_entropy_balanced_lower_bound_log_factorial_succ]
    ring_nf
  calc
    (r - s : ℝ) * Real.log (Nat.factorial q) +
        (s : ℝ) * Real.log (Nat.factorial (q + 1)) =
        (r : ℝ) * Real.log (q.factorial) + (s : ℝ) * Real.log (q + 1) := htarget
    _ =
        ∑ i : Fin r,
          (Real.log (q.factorial) + ((e i : ℝ) - (q : ℝ)) * Real.log (q + 1)) := by
          rw [hleft_sum]
    _ ≤ ∑ i, Real.log (Nat.factorial (e i)) := hsum_point

end Omega.Zeta
