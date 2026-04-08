import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic

namespace Omega.Conclusion

/-- lcm(8, 42) = 168.
    thm:conclusion-q13-crt-period-compression -/
theorem q13_lcm_8_42 : Nat.lcm 8 42 = 168 := by decide

/-- Iterated lcm chain collapses to 168.
    thm:conclusion-q13-crt-period-compression -/
theorem q13_lcm_chain : Nat.lcm (Nat.lcm 8 42) 168 = 168 := by decide

/-- Modulus factorisation 182 = 2·7·13.
    thm:conclusion-q13-crt-period-compression -/
theorem q13_modulus_factor : (182 : Nat) = 2 * 7 * 13 := by decide

/-- CRT period bound: any divisor-chain lcm fits inside 168.
    thm:conclusion-q13-crt-period-compression -/
theorem q13_crt_period_bound (p₂ p₇ p₁₃ : Nat)
    (h₂ : p₂ ∣ 8) (h₇ : p₇ ∣ 42) (h₁₃ : p₁₃ ∣ 168) :
    Nat.lcm (Nat.lcm p₂ p₇) p₁₃ ∣ 168 := by
  have hlcm27 : Nat.lcm p₂ p₇ ∣ Nat.lcm 8 42 :=
    lcm_dvd_lcm h₂ h₇
  have hlcm168 : Nat.lcm 8 42 = 168 := q13_lcm_8_42
  rw [hlcm168] at hlcm27
  have : Nat.lcm (Nat.lcm p₂ p₇) p₁₃ ∣ Nat.lcm 168 168 :=
    lcm_dvd_lcm hlcm27 h₁₃
  simpa using this

/-- Paper package: q=13 CRT period compression witnesses.
    thm:conclusion-q13-crt-period-compression -/
theorem paper_q13_crt_period_compression :
    (182 : Nat) = 2 * 7 * 13 ∧
    Nat.Coprime 2 7 ∧
    Nat.Coprime 14 13 ∧
    Nat.lcm 8 42 = 168 ∧
    Nat.lcm (Nat.lcm 8 42) 168 = 168 ∧
    (∀ p₂ p₇ p₁₃ : Nat, p₂ ∣ 8 → p₇ ∣ 42 → p₁₃ ∣ 168 →
      Nat.lcm (Nat.lcm p₂ p₇) p₁₃ ∣ 168) := by
  refine ⟨q13_modulus_factor, ?_, ?_, q13_lcm_8_42, q13_lcm_chain, ?_⟩
  · decide
  · decide
  · exact q13_crt_period_bound

end Omega.Conclusion
