import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic
import Omega.Zeta.EvenLengthCorrection

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

/-- Necklace correction kernel vanishes at odd lengths.
    cor:xi-time-part73c-fixed-parameter-necklace-correction -/
theorem paper_necklaceCorrectionKernel_odd_zero :
    (∀ v m : Nat, necklaceCorrectionKernel v (2 * m + 1) = 0) ∧
    necklaceCorrectionKernel 2 2 = 2 ∧
    necklaceCorrectionKernel 2 4 = 2 ∧
    necklaceCorrectionKernel 2 6 = 6 :=
  ⟨necklaceCorrectionKernel_odd_eq_zero,
   by native_decide, by native_decide, by native_decide⟩

-- ══════════════════════════════════════════════════════════════
-- Phase R301: Necklace correction kernel extended values
-- ══════════════════════════════════════════════════════════════

/-- Necklace correction kernel extended values for v=2.
    cor:xi-time-part73c-fixed-parameter-necklace-correction -/
theorem necklaceCorrectionKernel_values_extended :
    necklaceCorrectionKernel 2 8 = 12 ∧
    necklaceCorrectionKernel 2 10 = 30 ∧
    necklaceCorrectionKernel 2 12 = 54 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- Necklace correction kernel values for v=3 (ternary).
    cor:xi-time-part73c-fixed-parameter-necklace-correction -/
theorem necklaceCorrectionKernel_ternary :
    necklaceCorrectionKernel 3 2 = 3 ∧
    necklaceCorrectionKernel 3 4 = 6 ∧
    necklaceCorrectionKernel 3 6 = 24 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- Paper package.
    cor:xi-time-part73c-fixed-parameter-necklace-correction -/
theorem paper_necklaceCorrectionKernel_extended :
    (∀ v m : Nat, necklaceCorrectionKernel v (2 * m + 1) = 0) ∧
    necklaceCorrectionKernel 2 8 = 12 ∧
    necklaceCorrectionKernel 2 10 = 30 ∧
    necklaceCorrectionKernel 2 12 = 54 ∧
    necklaceCorrectionKernel 3 2 = 3 ∧
    necklaceCorrectionKernel 3 4 = 6 ∧
    necklaceCorrectionKernel 3 6 = 24 :=
  ⟨necklaceCorrectionKernel_odd_eq_zero,
   by native_decide, by native_decide, by native_decide,
   by native_decide, by native_decide, by native_decide⟩

/-- Necklace correction at v=2 for small even values.
    cor:xi-time-part73c-fixed-parameter-necklace-correction -/
theorem paper_necklace_correction_two_values :
    necklaceCorrectionKernel 2 2 = 2 ∧
    necklaceCorrectionKernel 2 4 = 2 ∧
    necklaceCorrectionKernel 2 6 = 6 ∧
    necklaceCorrectionKernel 2 8 = 12 ∧
    necklaceCorrectionKernel 2 10 = 30 ∧
    necklaceCorrectionKernel 2 12 = 54 := by
  refine ⟨by native_decide, by native_decide, by native_decide,
          by native_decide, by native_decide, by native_decide⟩

/-- Necklace correction at v=2 is positive for 1 ≤ m ≤ 20.
    cor:xi-time-part73c-fixed-parameter-necklace-correction -/
theorem necklaceCorrectionKernel_at_two_pos_bounded :
    ∀ m, 1 ≤ m → m ≤ 20 → 0 < necklaceCorrectionKernel 2 (2 * m) := by
  intro m hm hm'
  interval_cases m <;> native_decide

/-- At prime m=p: E(v,2p) - N(v,2p) = v^p + v.
    cor:xi-time-part73c-fixed-parameter-necklace-correction -/
theorem evenLength_sub_necklace_at_prime (v : Nat) {p : Nat} (hp : Nat.Prime p) :
    (evenLengthCorrection v (2 * p) : ℤ) - necklaceCorrectionKernel v (2 * p) =
    (v : ℤ) ^ p + v := by
  rw [evenLengthCorrection_even, necklaceCorrectionKernel_even]
  -- E = 2·v^p, N = Σ_{d|p} μ(d)·v^(p/d)
  -- divisors p = {1, p} for prime p
  have hDivs : Nat.divisors p = {1, p} := by
    ext d; simp only [Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro ⟨hd, hne⟩; exact (Nat.dvd_prime hp).mp hd
    · rintro (rfl | rfl) <;> simp [hp.ne_zero]
  rw [hDivs, Finset.sum_insert (show (1 : ℕ) ∉ ({p} : Finset ℕ) from by
    simp; exact hp.ne_one.symm), Finset.sum_singleton]
  rw [Nat.div_one, Nat.div_self hp.pos]
  have hμ1 : ArithmeticFunction.moebius 1 = (1 : ℤ) := by
    rw [ArithmeticFunction.moebius_apply_of_squarefree (by simp)]; norm_num
  have hμp : ArithmeticFunction.moebius p = (-1 : ℤ) := by
    rw [ArithmeticFunction.moebius_apply_of_squarefree hp.squarefree,
      ArithmeticFunction.cardFactors_apply_prime hp, pow_one]
  rw [hμ1, hμp]; push_cast; ring

end Omega.Zeta
