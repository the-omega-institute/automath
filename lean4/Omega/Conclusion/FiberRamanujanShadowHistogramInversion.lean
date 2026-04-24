import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped ArithmeticFunction.Moebius BigOperators

private theorem conclusion_fiber_ramanujan_shadow_histogram_inversion_hyperbola
    (M : Nat) (μf b : Nat → Int) :
    (∑ t ∈ Finset.range M,
        μf (t + 1) * (∑ u ∈ Finset.range (M / (t + 1)), b ((t + 1) * (u + 1)))) =
      ∑ n ∈ Finset.range M, (∑ d ∈ (n + 1).divisors, μf d) * b (n + 1) := by
  induction M with
  | zero =>
      simp
  | succ M ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hstep :
          (∑ t ∈ Finset.range M,
              μf (t + 1) * (∑ u ∈ Finset.range (Nat.succ M / (t + 1)), b ((t + 1) * (u + 1)))) =
            (∑ t ∈ Finset.range M,
              μf (t + 1) * (∑ u ∈ Finset.range (M / (t + 1)), b ((t + 1) * (u + 1)))) +
              ∑ t ∈ Finset.range M,
                if t + 1 ∣ Nat.succ M then μf (t + 1) * b (Nat.succ M) else (0 : Int) := by
        calc
          ∑ t ∈ Finset.range M,
              μf (t + 1) * (∑ u ∈ Finset.range (Nat.succ M / (t + 1)), b ((t + 1) * (u + 1)))
              =
              ∑ t ∈ Finset.range M,
                (μf (t + 1) * (∑ u ∈ Finset.range (M / (t + 1)), b ((t + 1) * (u + 1))) +
                  if t + 1 ∣ Nat.succ M then μf (t + 1) * b (Nat.succ M) else (0 : Int)) := by
                refine Finset.sum_congr rfl ?_
                intro t ht
                by_cases hdiv : t + 1 ∣ Nat.succ M
                · rw [Nat.succ_div_of_dvd hdiv, Finset.sum_range_succ, mul_add, if_pos hdiv]
                  have hmul : (t + 1) * ((M / (t + 1)) + 1) = Nat.succ M := by
                    rw [← Nat.succ_div_of_dvd hdiv, Nat.mul_div_cancel' hdiv]
                  simp [hmul]
                · rw [Nat.succ_div_of_not_dvd hdiv, if_neg hdiv]
                  simp
          _ =
              (∑ t ∈ Finset.range M,
                μf (t + 1) * (∑ u ∈ Finset.range (M / (t + 1)), b ((t + 1) * (u + 1)))) +
                ∑ t ∈ Finset.range M,
                  if t + 1 ∣ Nat.succ M then μf (t + 1) * b (Nat.succ M) else (0 : Int) := by
                rw [Finset.sum_add_distrib]
      rw [hstep, ih]
      have hdivsum :
          ∑ t ∈ Finset.range (M + 1),
              (if t + 1 ∣ Nat.succ M then μf (t + 1) * b (Nat.succ M) else (0 : Int)) =
            ∑ d ∈ (Nat.succ M).divisors, μf d * b (Nat.succ M) := by
        rw [← Nat.filter_dvd_eq_divisors (n := Nat.succ M) (Nat.succ_ne_zero M)]
        rw [Finset.sum_filter]
        simpa [Nat.succ_eq_add_one, add_assoc, add_left_comm, add_comm] using
          (Finset.sum_range_succ'
            (f := fun x =>
              if x ∣ Nat.succ M then μf x * b (Nat.succ M) else (0 : Int))
            (M + 1)).symm
      have htail :
          (∑ t ∈ Finset.range M,
              if t + 1 ∣ Nat.succ M then μf (t + 1) * b (Nat.succ M) else (0 : Int)) +
            μf (Nat.succ M) * b (Nat.succ M) =
          ∑ t ∈ Finset.range (M + 1),
              if t + 1 ∣ Nat.succ M then μf (t + 1) * b (Nat.succ M) else (0 : Int) := by
        rw [Finset.sum_range_succ]
        simp
      have hsingle :
          μf (Nat.succ M) * ∑ x ∈ Finset.range 1, b ((Nat.succ M) * (x + 1)) =
            μf (Nat.succ M) * b (Nat.succ M) := by
        simp
      simp only [Nat.succ_eq_add_one, Nat.div_self (Nat.succ_pos M)]
      rw [hsingle, add_assoc, htail, hdivsum]
      simpa [Nat.succ_eq_add_one, Finset.sum_mul]

private theorem conclusion_fiber_ramanujan_shadow_histogram_inversion_moebius_sum
    (n : Nat) :
    (∑ d ∈ (n + 1).divisors, (ArithmeticFunction.moebius d : Int)) = if n = 0 then 1 else 0 := by
  have hprod : (ArithmeticFunction.moebius * ArithmeticFunction.zeta : ArithmeticFunction Int) = 1 :=
    ArithmeticFunction.moebius_mul_coe_zeta
  have happly :
      ((ArithmeticFunction.moebius * ArithmeticFunction.zeta : ArithmeticFunction Int) (n + 1)) =
        (1 : ArithmeticFunction Int) (n + 1) := by
    exact congrArg (fun F : ArithmeticFunction Int => F (n + 1)) hprod
  have hconv :
      (∑ d ∈ (n + 1).divisors, (ArithmeticFunction.moebius d : Int)) =
        (1 : ArithmeticFunction Int) (n + 1) := by
    rw [← ArithmeticFunction.coe_mul_zeta_apply]
    exact happly
  rcases eq_or_ne n 0 with rfl | hn
  · simpa [ArithmeticFunction.one_apply] using hconv
  · have hne : n + 1 ≠ 1 := by
      intro h
      apply hn
      simpa using Nat.succ.inj h
    simpa [hn, ArithmeticFunction.one_apply_ne hne] using hconv

theorem paper_conclusion_fiber_ramanujan_shadow_histogram_inversion
    (D : Nat) (N h : Nat → Int)
    (hN : ∀ r, 1 ≤ r → r ≤ D →
      N r = ∑ t ∈ Finset.range (D / r), h (r * (t + 1))) :
    ∀ s, 1 ≤ s → s ≤ D →
      h s = ∑ t ∈ Finset.range (D / s), (ArithmeticFunction.moebius (t + 1) : Int) * N (s * (t + 1)) := by
  intro s hs hsD
  let M := D / s
  have hMpos : 0 < M := by
    dsimp [M]
    exact Nat.div_pos hsD hs
  have hsum :
      ∑ t ∈ Finset.range M, (ArithmeticFunction.moebius (t + 1) : Int) * N (s * (t + 1)) =
        ∑ n ∈ Finset.range M,
          (∑ d ∈ (n + 1).divisors, (ArithmeticFunction.moebius d : Int)) * h (s * (n + 1)) := by
    dsimp [M]
    calc
      ∑ t ∈ Finset.range (D / s), (ArithmeticFunction.moebius (t + 1) : Int) * N (s * (t + 1))
          = ∑ t ∈ Finset.range (D / s),
              (ArithmeticFunction.moebius (t + 1) : Int) *
                (∑ u ∈ Finset.range ((D / s) / (t + 1)), h (s * ((t + 1) * (u + 1)))) := by
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
      _ = ∑ n ∈ Finset.range (D / s),
            (∑ d ∈ (n + 1).divisors, (ArithmeticFunction.moebius d : Int)) * h (s * (n + 1)) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              conclusion_fiber_ramanujan_shadow_histogram_inversion_hyperbola
                (D / s) (fun n => (ArithmeticFunction.moebius n : Int)) (fun n => h (s * n))
  have hcollapse :
      ∑ n ∈ Finset.range M,
          (∑ d ∈ (n + 1).divisors, (ArithmeticFunction.moebius d : Int)) * h (s * (n + 1)) =
        h s := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hMpos.ne'
    rw [hm]
    simp [conclusion_fiber_ramanujan_shadow_histogram_inversion_moebius_sum]
  calc
    h s = ∑ n ∈ Finset.range M,
        (∑ d ∈ (n + 1).divisors, (ArithmeticFunction.moebius d : Int)) * h (s * (n + 1)) := by
          symm
          exact hcollapse
    _ = ∑ t ∈ Finset.range M, (ArithmeticFunction.moebius (t + 1) : Int) * N (s * (t + 1)) := by
          symm
          exact hsum

end Omega.Conclusion
