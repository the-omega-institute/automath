import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators ArithmeticFunction.Moebius

private theorem conclusion_fiber_ramanujan_shadow_histogram_inversion_hyperbola
    (M : Nat) (μf b : Nat → Int) :
    (∑ t in Finset.range M,
        μf (t + 1) * ∑ u in Finset.range (M / (t + 1)), b ((t + 1) * (u + 1))) =
      ∑ n in Finset.range M, (∑ d in (n + 1).divisors, μf d) * b (n + 1) := by
  induction M with
  | zero =>
      simp
  | succ M ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      have hstep :
          (∑ t in Finset.range M,
              μf (t + 1) * ∑ u in Finset.range (Nat.succ M / (t + 1)), b ((t + 1) * (u + 1))) =
            (∑ t in Finset.range M,
              μf (t + 1) * ∑ u in Finset.range (M / (t + 1)), b ((t + 1) * (u + 1))) +
              ∑ t in Finset.range M,
                if t + 1 ∣ Nat.succ M then μf (t + 1) * b (Nat.succ M) else 0 := by
        refine Finset.sum_congr rfl ?_
        intro t ht
        by_cases hdiv : t + 1 ∣ Nat.succ M
        · rw [Nat.succ_div_of_dvd hdiv, Finset.sum_range_succ, mul_add, if_pos hdiv]
          have hmul : (t + 1) * ((M / (t + 1)) + 1) = Nat.succ M := by
            rw [← Nat.succ_div_of_dvd hdiv, Nat.mul_div_cancel' hdiv]
          simp [hmul]
        · rw [Nat.succ_div_of_not_dvd hdiv, if_neg hdiv]
      rw [hstep]
      have hdivsum :
          ∑ t in Finset.range (M + 1),
              (if t + 1 ∣ Nat.succ M then μf (t + 1) * b (Nat.succ M) else 0) =
            ∑ d in (Nat.succ M).divisors, μf d * b (Nat.succ M) := by
        rw [← Nat.filter_dvd_eq_divisors (n := Nat.succ M) (Nat.succ_ne_zero M)]
        rw [Finset.sum_filter, Finset.sum_range_succ']
        simp
      simp only [Nat.succ_eq_add_one, Finset.sum_range_succ, Nat.succ_div_self, mul_one]
      rw [← add_assoc, hdivsum]

private theorem conclusion_fiber_ramanujan_shadow_histogram_inversion_moebius_sum
    (n : Nat) :
    (∑ d in (n + 1).divisors, (ArithmeticFunction.moebius d : Int)) = if n = 0 then 1 else 0 := by
  have hconv := congrArg (fun F : ArithmeticFunction Int => F (n + 1))
    (ArithmeticFunction.moebius_mul_coe_zeta)
  simpa [ArithmeticFunction.coe_mul_zeta_apply] using hconv

theorem paper_conclusion_fiber_ramanujan_shadow_histogram_inversion
    (D : Nat) (N h : Nat → Int)
    (hN : ∀ r, 1 ≤ r → r ≤ D →
      N r = ∑ t in Finset.range (D / r), h (r * (t + 1))) :
    ∀ s, 1 ≤ s → s ≤ D →
      h s = ∑ t in Finset.range (D / s), (ArithmeticFunction.moebius (t + 1) : Int) * N (s * (t + 1)) := by
  intro s hs hsD
  let M := D / s
  have hMpos : 0 < M := by
    dsimp [M]
    exact Nat.div_pos hsD hs
  have hsum :
      ∑ t in Finset.range M, (ArithmeticFunction.moebius (t + 1) : Int) * N (s * (t + 1)) =
        ∑ n in Finset.range M,
          (∑ d in (n + 1).divisors, (ArithmeticFunction.moebius d : Int)) * h (s * (n + 1)) := by
    dsimp [M]
    calc
      ∑ t in Finset.range (D / s), (ArithmeticFunction.moebius (t + 1) : Int) * N (s * (t + 1))
          = ∑ t in Finset.range (D / s),
              (ArithmeticFunction.moebius (t + 1) : Int) *
                (∑ u in Finset.range ((D / s) / (t + 1)), h (s * ((t + 1) * (u + 1)))) := by
                refine Finset.sum_congr rfl ?_
                intro t ht
                have htbound : t + 1 ≤ D / s := Nat.succ_le_of_lt (Finset.mem_range.mp ht)
                have hst : s * (t + 1) ≤ D := by
                  calc
                    s * (t + 1) ≤ s * (D / s) := Nat.mul_le_mul_left _ htbound
                    _ ≤ D := Nat.mul_div_le D s
                rw [hN (s * (t + 1)) (Nat.mul_pos hs (Nat.succ_pos _)) hst]
                congr 1
                rw [Nat.div_div_eq_div_mul]
                ring
      _ = ∑ n in Finset.range (D / s),
            (∑ d in (n + 1).divisors, (ArithmeticFunction.moebius d : Int)) * h (s * (n + 1)) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              conclusion_fiber_ramanujan_shadow_histogram_inversion_hyperbola
                (D / s) (fun n => (ArithmeticFunction.moebius n : Int)) (fun n => h (s * n))
  have hcollapse :
      ∑ n in Finset.range M,
          (∑ d in (n + 1).divisors, (ArithmeticFunction.moebius d : Int)) * h (s * (n + 1)) =
        h s := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hMpos.ne'
    rw [hm]
    simp [conclusion_fiber_ramanujan_shadow_histogram_inversion_moebius_sum, hs]
  calc
    h s = ∑ n in Finset.range M,
        (∑ d in (n + 1).divisors, (ArithmeticFunction.moebius d : Int)) * h (s * (n + 1)) := by
          symm
          exact hcollapse
    _ = ∑ t in Finset.range M, (ArithmeticFunction.moebius (t + 1) : Int) * N (s * (t + 1)) := by
          symm
          exact hsum

end Omega.Conclusion
