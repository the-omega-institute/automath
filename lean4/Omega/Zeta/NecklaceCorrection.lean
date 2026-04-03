import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Fixed-parameter necklace correction kernel.
    cor:xi-time-part73c-fixed-parameter-necklace-correction -/
def necklaceCorrectionKernel (v n : Nat) : Int :=
  if Even n then
    Finset.sum (Nat.divisors (n / 2)) (fun d => ArithmeticFunction.moebius d * (v : Int) ^ ((n / 2) / d))
  else 0

/-- Odd lengths contribute zero to the necklace correction kernel.
    cor:xi-time-part73c-fixed-parameter-necklace-correction -/
theorem necklaceCorrectionKernel_odd (v n : Nat) (hn : ¬ Even n) :
    necklaceCorrectionKernel v n = 0 := by
  simp [necklaceCorrectionKernel, hn]

/-- Even lengths reduce to the divisor-sum correction formula.
    cor:xi-time-part73c-fixed-parameter-necklace-correction -/
theorem necklaceCorrectionKernel_even (v m : Nat) :
    necklaceCorrectionKernel v (2 * m) =
      Finset.sum (Nat.divisors m) (fun d => ArithmeticFunction.moebius d * (v : Int) ^ (m / d)) := by
  simp [necklaceCorrectionKernel]

/-- Every odd successor length has zero correction.
    cor:xi-time-part73c-fixed-parameter-necklace-correction -/
theorem necklaceCorrectionKernel_odd_eq_zero (v m : Nat) :
    necklaceCorrectionKernel v (2 * m + 1) = 0 := by
  simp [necklaceCorrectionKernel]

/-- Unified divisor form of the necklace correction kernel.
    cor:xi-time-part73c-fixed-parameter-necklace-correction -/
theorem necklaceCorrectionKernel_divisor_form (v n : Nat) :
    necklaceCorrectionKernel v n =
      Finset.sum ((Nat.divisors n).filter (fun d => Even (n / d)))
        (fun d => ArithmeticFunction.moebius d * (v : Int) ^ ((n / d) / 2)) := by
  by_cases hn : Even n
  · rcases hn with ⟨m, hm⟩
    rw [hm, show m + m = 2 * m by omega, necklaceCorrectionKernel_even]
    have hfilter :
        (Nat.divisors (2 * m)).filter (fun d => Even ((2 * m) / d)) = Nat.divisors m := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hdvd, hne⟩, hEven⟩
        refine ⟨?_, by omega⟩
        rcases hEven with ⟨k, hk⟩
        refine ⟨k, ?_⟩
        have hmul : d * ((2 * m) / d) = d * (k + k) := by rw [hk]
        have hmul' : 2 * m = d * (k + k) := by
          calc
            2 * m = d * ((2 * m) / d) := (Nat.mul_div_cancel' hdvd).symm
            _ = d * (k + k) := hmul
        have hmul'' : 2 * m = 2 * (d * k) := by
          calc
            2 * m = d * (k + k) := hmul'
            _ = d * k + d * k := by rw [Nat.mul_add]
            _ = 2 * (d * k) := by rw [← two_mul]
        exact Nat.eq_of_mul_eq_mul_left (by omega) hmul''
      · rintro ⟨hdvd, hmne⟩
        refine ⟨?_, ?_⟩
        · exact ⟨dvd_mul_of_dvd_right hdvd 2, by omega⟩
        · rcases hdvd with ⟨k, hk⟩
          refine ⟨k, ?_⟩
          have hdne : d ≠ 0 := by
            intro hd0
            subst hd0
            have hm0 : m = 0 := by simpa using hk
            exact hmne hm0
          rw [hk]
          calc
            (2 * (d * k)) / d = ((2 * k) * d) / d := by ring_nf
            _ = 2 * k := by
              have hq : d * (2 * k) / d = 2 * k := Nat.mul_div_right (2 * k) (Nat.pos_of_ne_zero hdne)
              simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hq
            _ = k + k := by rw [two_mul]
    rw [hfilter]
    refine Finset.sum_congr rfl ?_
    intro d hd
    have hdvd : d ∣ m := Nat.dvd_of_mem_divisors hd
    have hhalf : (m / d) * 2 / 2 = m / d := by
      rw [Nat.mul_comm, Nat.mul_div_right _ (by decide)]
    rw [Nat.mul_div_assoc 2 hdvd, show 2 * (m / d) = (m / d) * 2 by rw [Nat.mul_comm], hhalf]
  · rw [necklaceCorrectionKernel_odd v n hn]
    symm
    apply Finset.sum_eq_zero
    intro d hd
    have hdmem : d ∈ (Nat.divisors n).filter (fun d => Even (n / d)) := by simpa using hd
    exfalso
    have hdvd : d ∣ n := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hdmem).1
    have hEven : Even (n / d) := (Finset.mem_filter.mp hdmem).2
    apply hn
    rcases hEven with ⟨k, hk⟩
    refine ⟨d * k, ?_⟩
    calc
      n = d * (n / d) := (Nat.mul_div_cancel' hdvd).symm
      _ = d * (k + k) := by rw [hk]
      _ = d * k + d * k := by rw [Nat.mul_add]
      _ = 2 * (d * k) := by rw [← two_mul]
      _ = d * k + d * k := by rw [two_mul]

end Omega.Zeta
