import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

namespace Omega.GU

private lemma prime_log_ratio_irrational {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) : Irrational (Real.log (p : ℝ) / Real.log (q : ℝ)) := by
  rw [Irrational]
  intro hRat
  rcases hRat with ⟨r, hr⟩
  let k : ℕ := Int.toNat r.num
  have hp_gt : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hq_gt : 1 < (q : ℝ) := by exact_mod_cast hq.one_lt
  have hp_pos : 0 < (p : ℝ) := by positivity
  have hq_pos : 0 < (q : ℝ) := by positivity
  have hp_log_pos : 0 < Real.log (p : ℝ) := Real.log_pos hp_gt
  have hq_log_pos : 0 < Real.log (q : ℝ) := Real.log_pos hq_gt
  have hq_log_ne : Real.log (q : ℝ) ≠ 0 := hq_log_pos.ne'
  have hratio_pos : 0 < Real.log (p : ℝ) / Real.log (q : ℝ) := by
    exact div_pos hp_log_pos hq_log_pos
  have hr_pos_real : (0 : ℝ) < r := by
    simpa [hr] using hratio_pos
  have hr_pos : 0 < r := by
    exact (Rat.cast_pos (K := ℝ) (q := r)).mp hr_pos_real
  have hnum_pos : 0 < r.num := Rat.num_pos.mpr hr_pos
  have hnum_ne : r.num ≠ 0 := ne_of_gt hnum_pos
  have hk_ne : k ≠ 0 := by
    intro hk0
    have hk0' : Int.toNat r.num = 0 := by simpa [k] using hk0
    have hk0_le : r.num ≤ 0 := Int.toNat_eq_zero.mp hk0'
    exact (not_le_of_gt hnum_pos) hk0_le
  have hk_cast_int : (k : ℤ) = r.num := by
    simpa [k] using Int.toNat_of_nonneg hnum_pos.le
  have hk_cast : (k : ℝ) = (r.num : ℝ) := by
    exact_mod_cast hk_cast_int
  have hden_ne : (r.den : ℝ) ≠ 0 := by positivity
  have hratio : Real.log (p : ℝ) / Real.log (q : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by
    simpa [Rat.cast_def] using hr.symm
  have hcross : (r.den : ℝ) * Real.log (p : ℝ) = (r.num : ℝ) * Real.log (q : ℝ) := by
    field_simp [hq_log_ne, hden_ne] at hratio
    linarith
  have hpow_log : (r.den : ℝ) * Real.log (p : ℝ) = (k : ℝ) * Real.log (q : ℝ) := by
    rw [hk_cast]
    exact hcross
  have hpow_real : (p : ℝ) ^ r.den = (q : ℝ) ^ k := by
    calc
      (p : ℝ) ^ r.den = Real.exp ((r.den : ℝ) * Real.log (p : ℝ)) := by
        rw [Real.exp_nat_mul, Real.exp_log hp_pos]
      _ = Real.exp ((k : ℝ) * Real.log (q : ℝ)) := by rw [hpow_log]
      _ = (q : ℝ) ^ k := by
        rw [Real.exp_nat_mul, Real.exp_log hq_pos]
  have hpow_nat : p ^ r.den = q ^ k := by
    exact_mod_cast hpow_real
  have hp_eq_q : p = q :=
    (Nat.Prime.pow_inj' hp hq (Nat.ne_zero_of_lt r.den_pos) hk_ne hpow_nat).1
  exact hpq hp_eq_q

/-- Equality of the two prime Euler phases forces the time parameter to agree.
    thm:group-jg-two-prime-euler-phase-injective -/
theorem paper_group_jg_two_prime_euler_phase_injective {p q : ℕ} (hp : Nat.Prime p)
    (hq : Nat.Prime q) (hpq : p ≠ q) :
    Function.Injective
      (fun t : ℝ =>
        (Complex.exp (Complex.I * (t * Real.log (p : ℝ))),
          Complex.exp (Complex.I * (t * Real.log (q : ℝ))))) := by
  intro t₁ t₂ h
  by_contra hneq
  have hp_eq : Complex.exp (Complex.I * (t₁ * Real.log (p : ℝ))) =
      Complex.exp (Complex.I * (t₂ * Real.log (p : ℝ))) := by
    simpa using congrArg Prod.fst h
  have hq_eq : Complex.exp (Complex.I * (t₁ * Real.log (q : ℝ))) =
      Complex.exp (Complex.I * (t₂ * Real.log (q : ℝ))) := by
    simpa using congrArg Prod.snd h
  rcases (Complex.exp_eq_exp_iff_exists_int.mp hp_eq) with ⟨m, hm⟩
  rcases (Complex.exp_eq_exp_iff_exists_int.mp hq_eq) with ⟨n, hn⟩
  have hm_im := congrArg Complex.im hm
  have hn_im := congrArg Complex.im hn
  have hm_im'' : t₁ * (Complex.log (p : ℂ)).re =
      t₂ * (Complex.log (p : ℂ)).re + (m : ℝ) * (2 * Real.pi) := by
    simpa [mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using hm_im
  have hn_im'' : t₁ * (Complex.log (q : ℂ)).re =
      t₂ * (Complex.log (q : ℂ)).re + (n : ℝ) * (2 * Real.pi) := by
    simpa [mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using hn_im
  have hp_log_re : (Complex.log (p : ℂ)).re = Real.log (p : ℝ) := by
    simpa using (Complex.log_ofReal_re (p : ℝ))
  have hq_log_re : (Complex.log (q : ℂ)).re = Real.log (q : ℝ) := by
    simpa using (Complex.log_ofReal_re (q : ℝ))
  have hm_im' : t₁ * Real.log (p : ℝ) = t₂ * Real.log (p : ℝ) + (m : ℝ) * (2 * Real.pi) := by
    simpa [hp_log_re] using hm_im''
  have hn_im' : t₁ * Real.log (q : ℝ) = t₂ * Real.log (q : ℝ) + (n : ℝ) * (2 * Real.pi) := by
    simpa [hq_log_re] using hn_im''
  have hm_period : (t₁ - t₂) * Real.log (p : ℝ) = (m : ℝ) * (2 * Real.pi) := by
    linarith
  have hn_period : (t₁ - t₂) * Real.log (q : ℝ) = (n : ℝ) * (2 * Real.pi) := by
    linarith
  have hp_gt : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hq_gt : 1 < (q : ℝ) := by exact_mod_cast hq.one_lt
  have hp_log_pos : 0 < Real.log (p : ℝ) := Real.log_pos hp_gt
  have hq_log_pos : 0 < Real.log (q : ℝ) := Real.log_pos hq_gt
  have hp_log_ne : Real.log (p : ℝ) ≠ 0 := hp_log_pos.ne'
  have hq_log_ne : Real.log (q : ℝ) ≠ 0 := hq_log_pos.ne'
  have hdt_ne : t₁ - t₂ ≠ 0 := sub_ne_zero.mpr hneq
  have hm_ne : m ≠ 0 := by
    intro hm0
    have hm0_real : (m : ℝ) = 0 := by exact_mod_cast hm0
    have hm_period' : (t₁ - t₂) * Real.log (p : ℝ) = 0 := by
      simpa [hm0_real] using hm_period
    have hm_period'' : (t₁ - t₂) * Real.log (p : ℝ) = 0 * Real.log (p : ℝ) := by
      simpa using hm_period'
    have : t₁ - t₂ = 0 := mul_right_cancel₀ hp_log_ne hm_period''
    exact hdt_ne this
  have hn_ne : n ≠ 0 := by
    intro hn0
    have hn0_real : (n : ℝ) = 0 := by exact_mod_cast hn0
    have hn_period' : (t₁ - t₂) * Real.log (q : ℝ) = 0 := by
      simpa [hn0_real] using hn_period
    have hn_period'' : (t₁ - t₂) * Real.log (q : ℝ) = 0 * Real.log (q : ℝ) := by
      simpa using hn_period'
    have : t₁ - t₂ = 0 := mul_right_cancel₀ hq_log_ne hn_period''
    exact hdt_ne this
  have hn_real_ne : (n : ℝ) ≠ 0 := by
    exact_mod_cast hn_ne
  have htwoPi_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hm_div : Real.log (p : ℝ) = ((m : ℝ) * (2 * Real.pi)) / (t₁ - t₂) := by
    apply (eq_div_iff hdt_ne).2
    simpa [mul_comm] using hm_period
  have hn_div : Real.log (q : ℝ) = ((n : ℝ) * (2 * Real.pi)) / (t₁ - t₂) := by
    apply (eq_div_iff hdt_ne).2
    simpa [mul_comm] using hn_period
  have hratio : Real.log (p : ℝ) / Real.log (q : ℝ) = (m : ℝ) / (n : ℝ) := by
    rw [hm_div, hn_div]
    field_simp [hdt_ne, hn_real_ne, htwoPi_ne]
  exact
    ((irrational_iff_ne_rational _).mp (prime_log_ratio_irrational hp hq hpq) m n hn_ne) hratio

end Omega.GU
