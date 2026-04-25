import Mathlib
import Omega.SyncKernelWeighted.RealInput40TraceRecurrence

namespace Omega.SyncKernelWeighted

open scoped ArithmeticFunction.Moebius BigOperators

/-- The Möbius inverse of `n ↦ (-1)^n` is supported on `1` and `2`. -/
private def real_input_40_primitive_lucas_simplified_sign_inverse (n : ℕ) : ℚ :=
  if n = 1 then -1 else if n = 2 then 2 else 0

private theorem real_input_40_primitive_lucas_simplified_sign_sum (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors, real_input_40_primitive_lucas_simplified_sign_inverse d) = (-1 : ℚ) ^ n := by
  by_cases heven : Even n
  · have h1 : 1 ∈ n.divisors := by
      simp [Nat.mem_divisors, hn.ne']
    have h2 : 2 ∈ n.divisors := by
      simp [Nat.mem_divisors, hn.ne', heven.two_dvd]
    have h2erase : 2 ∈ n.divisors.erase 1 := by
      simp [h2]
    have hsplit2 :
        ∑ d ∈ n.divisors.erase 1, real_input_40_primitive_lucas_simplified_sign_inverse d =
          real_input_40_primitive_lucas_simplified_sign_inverse 2 +
            ∑ d ∈ (n.divisors.erase 1).erase 2,
              real_input_40_primitive_lucas_simplified_sign_inverse d := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (Finset.sum_erase_add (s := n.divisors.erase 1)
          (f := real_input_40_primitive_lucas_simplified_sign_inverse) h2erase).symm
    have htail_zero :
        ∑ d ∈ (n.divisors.erase 1).erase 2,
          real_input_40_primitive_lucas_simplified_sign_inverse d = 0 := by
      refine Finset.sum_eq_zero ?_
      intro b hb
      have hb2 : b ≠ 2 := (Finset.mem_erase.mp hb).1
      have hb1 : b ≠ 1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hb).2).1
      simp [real_input_40_primitive_lucas_simplified_sign_inverse, hb1, hb2]
    calc
      (∑ d ∈ n.divisors, real_input_40_primitive_lucas_simplified_sign_inverse d)
          = real_input_40_primitive_lucas_simplified_sign_inverse 1 +
              ∑ d ∈ n.divisors.erase 1, real_input_40_primitive_lucas_simplified_sign_inverse d := by
              simpa [add_comm, add_left_comm, add_assoc] using
                (Finset.sum_erase_add (s := n.divisors)
                  (f := real_input_40_primitive_lucas_simplified_sign_inverse) h1).symm
      _ = real_input_40_primitive_lucas_simplified_sign_inverse 1 +
            (real_input_40_primitive_lucas_simplified_sign_inverse 2 +
              ∑ d ∈ (n.divisors.erase 1).erase 2,
                real_input_40_primitive_lucas_simplified_sign_inverse d) := by
              rw [hsplit2]
      _ = (-1 : ℚ) ^ n := by
        rw [htail_zero, heven.neg_one_pow]
        norm_num [real_input_40_primitive_lucas_simplified_sign_inverse]
  · have hodd : Odd n := Nat.not_even_iff_odd.mp heven
    have h1 : 1 ∈ n.divisors := by
      simp [Nat.mem_divisors, hn.ne']
    have h2not : 2 ∉ n.divisors := by
      intro h2
      exact heven (even_iff_two_dvd.2 (by simpa [Nat.mem_divisors, hn.ne'] using h2))
    have hrest_zero :
        ∑ d ∈ n.divisors.erase 1, real_input_40_primitive_lucas_simplified_sign_inverse d = 0 := by
      refine Finset.sum_eq_zero ?_
      intro b hb
      have hb1 : b ≠ 1 := (Finset.mem_erase.mp hb).1
      have hb2 : b ≠ 2 := by
        intro hb2
        exact h2not (hb2 ▸ (Finset.mem_erase.mp hb).2)
      simp [real_input_40_primitive_lucas_simplified_sign_inverse, hb1, hb2]
    calc
      (∑ d ∈ n.divisors, real_input_40_primitive_lucas_simplified_sign_inverse d)
          = real_input_40_primitive_lucas_simplified_sign_inverse 1 +
              ∑ d ∈ n.divisors.erase 1, real_input_40_primitive_lucas_simplified_sign_inverse d := by
              simpa [add_comm, add_left_comm, add_assoc] using
                (Finset.sum_erase_add (s := n.divisors)
                  (f := real_input_40_primitive_lucas_simplified_sign_inverse) h1).symm
      _ = (-1 : ℚ) ^ n := by
        rw [hrest_zero, hodd.neg_one_pow]
        norm_num [real_input_40_primitive_lucas_simplified_sign_inverse]

private theorem real_input_40_primitive_lucas_simplified_signed_moebius (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℚ) * (-1 : ℚ) ^ (n / d)) =
      real_input_40_primitive_lucas_simplified_sign_inverse n := by
  have hmobius :=
    (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
      (f := real_input_40_primitive_lucas_simplified_sign_inverse)
      (g := fun m => (-1 : ℚ) ^ m)).mp real_input_40_primitive_lucas_simplified_sign_sum
  have hanti := hmobius n hn
  rw [Nat.sum_divisorsAntidiagonal
      (f := fun d m => (ArithmeticFunction.moebius d : ℚ) * (-1 : ℚ) ^ m)] at hanti
  exact hanti

private theorem real_input_40_primitive_lucas_simplified_moebius_sum_zero (n : ℕ) (hn : 2 < n) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℚ)) = 0 := by
  have hn1 : n ≠ 1 := by omega
  calc
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℚ))
        = (((ArithmeticFunction.moebius : ArithmeticFunction ℚ) * ArithmeticFunction.zeta) n) := by
            simpa using
              (ArithmeticFunction.coe_mul_zeta_apply
                (f := (ArithmeticFunction.moebius : ArithmeticFunction ℚ)) (x := n)).symm
    _ = (1 : ArithmeticFunction ℚ) n := by simp
    _ = 0 := by simp [hn1]

private theorem real_input_40_primitive_lucas_simplified_signed_sum_zero (n : ℕ) (hn : 2 < n) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℚ) * (-1 : ℚ) ^ (n / d)) = 0 := by
  have hpos : 0 < n := by omega
  rw [real_input_40_primitive_lucas_simplified_signed_moebius n hpos]
  have hn1 : n ≠ 1 := by omega
  have hn2 : n ≠ 2 := by omega
  simp [real_input_40_primitive_lucas_simplified_sign_inverse, hn1, hn2]

private theorem real_input_40_primitive_lucas_simplified_trace_rewrite (m : ℕ) :
    (realInput40TraceSequence m : ℚ) =
      (Omega.lucasNum (2 * m) : ℚ) + (-1 : ℚ) ^ m * (Omega.lucasNum m : ℚ) +
        (3 * (-1 : ℚ) ^ m + 2) := by
  have hdouble : (Omega.lucasNum (2 * m) : ℚ) = (Omega.lucasNum m : ℚ) ^ 2 - 2 * (-1 : ℚ) ^ m := by
    exact_mod_cast Omega.lucasNum_double_uncond m
  calc
    (realInput40TraceSequence m : ℚ)
        = (Omega.lucasNum m : ℚ) ^ 2 + (-1 : ℚ) ^ m * ((Omega.lucasNum m : ℚ) + 1) + 2 := by
            norm_num [realInput40TraceSequence]
    _ = (Omega.lucasNum (2 * m) : ℚ) + (-1 : ℚ) ^ m * (Omega.lucasNum m : ℚ) +
          (3 * (-1 : ℚ) ^ m + 2) := by
            rw [hdouble]
            ring

/-- Paper label: `cor:real-input-40-primitive-lucas-simplified`. -/
theorem paper_real_input_40_primitive_lucas_simplified : ∀ n : ℕ, 2 < n →
    (1 / (n : ℚ)) * Finset.sum n.divisors
      (fun d => (ArithmeticFunction.moebius d : ℚ) * (realInput40TraceSequence (n / d) : ℚ)) =
    (1 / (n : ℚ)) * Finset.sum n.divisors
      (fun d => (ArithmeticFunction.moebius d : ℚ) *
        ((Omega.lucasNum (2 * (n / d)) : ℚ) + (-1 : ℚ) ^ (n / d) * (Omega.lucasNum (n / d) : ℚ))) := by
  intro n hn
  have hsigned_zero := real_input_40_primitive_lucas_simplified_signed_sum_zero n hn
  have hmu_zero := real_input_40_primitive_lucas_simplified_moebius_sum_zero n hn
  have hsum :
      Finset.sum n.divisors
          (fun d => (ArithmeticFunction.moebius d : ℚ) * (realInput40TraceSequence (n / d) : ℚ)) =
        Finset.sum n.divisors
          (fun d => (ArithmeticFunction.moebius d : ℚ) *
            ((Omega.lucasNum (2 * (n / d)) : ℚ) + (-1 : ℚ) ^ (n / d) * (Omega.lucasNum (n / d) : ℚ))) +
          3 * Finset.sum n.divisors (fun d => (ArithmeticFunction.moebius d : ℚ) * (-1 : ℚ) ^ (n / d)) +
          2 * Finset.sum n.divisors (fun d => (ArithmeticFunction.moebius d : ℚ)) := by
    calc
      Finset.sum n.divisors
          (fun d => (ArithmeticFunction.moebius d : ℚ) * (realInput40TraceSequence (n / d) : ℚ))
          =
        Finset.sum n.divisors
          (fun d => (ArithmeticFunction.moebius d : ℚ) *
            (((Omega.lucasNum (2 * (n / d)) : ℚ) + (-1 : ℚ) ^ (n / d) * (Omega.lucasNum (n / d) : ℚ)) +
              (3 * (-1 : ℚ) ^ (n / d) + 2))) := by
            refine Finset.sum_congr rfl ?_
            intro d hd
            rw [real_input_40_primitive_lucas_simplified_trace_rewrite (n / d)]
      _ =
        Finset.sum n.divisors
          (fun d => (ArithmeticFunction.moebius d : ℚ) *
            ((Omega.lucasNum (2 * (n / d)) : ℚ) + (-1 : ℚ) ^ (n / d) * (Omega.lucasNum (n / d) : ℚ)) +
              (3 * ((ArithmeticFunction.moebius d : ℚ) * (-1 : ℚ) ^ (n / d)) +
                2 * (ArithmeticFunction.moebius d : ℚ))) := by
            refine Finset.sum_congr rfl ?_
            intro d hd
            ring
      _ =
        Finset.sum n.divisors
          (fun d => (ArithmeticFunction.moebius d : ℚ) *
            ((Omega.lucasNum (2 * (n / d)) : ℚ) + (-1 : ℚ) ^ (n / d) * (Omega.lucasNum (n / d) : ℚ))) +
          3 * Finset.sum n.divisors (fun d => (ArithmeticFunction.moebius d : ℚ) * (-1 : ℚ) ^ (n / d)) +
          2 * Finset.sum n.divisors (fun d => (ArithmeticFunction.moebius d : ℚ)) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
            ring
  calc
    (1 / (n : ℚ)) * Finset.sum n.divisors
        (fun d => (ArithmeticFunction.moebius d : ℚ) * (realInput40TraceSequence (n / d) : ℚ))
        =
      (1 / (n : ℚ)) *
        (Finset.sum n.divisors
            (fun d => (ArithmeticFunction.moebius d : ℚ) *
              ((Omega.lucasNum (2 * (n / d)) : ℚ) + (-1 : ℚ) ^ (n / d) * (Omega.lucasNum (n / d) : ℚ))) +
          3 * Finset.sum n.divisors (fun d => (ArithmeticFunction.moebius d : ℚ) * (-1 : ℚ) ^ (n / d)) +
          2 * Finset.sum n.divisors (fun d => (ArithmeticFunction.moebius d : ℚ))) := by
            rw [hsum]
    _ = (1 / (n : ℚ)) * Finset.sum n.divisors
          (fun d => (ArithmeticFunction.moebius d : ℚ) *
            ((Omega.lucasNum (2 * (n / d)) : ℚ) + (-1 : ℚ) ^ (n / d) * (Omega.lucasNum (n / d) : ℚ))) := by
            rw [hsigned_zero, hmu_zero]
            ring

end Omega.SyncKernelWeighted
