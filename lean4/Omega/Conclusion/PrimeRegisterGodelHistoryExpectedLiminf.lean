import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.CircleDimension.GodelPrimeBitlengthLowerBound
import Omega.Conclusion.PrimeRegister
import Omega.EA.DynamicPrimeRegisterBitlength

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-godel-history-expected-liminf`. If the dynamic Gödel history has
one active event on each of the first `m` slices, then the existing factorial lower bound applies
to the code value, and the bitlength witness yields a normalized `m log m` lower bound once
`m ≥ 2`. -/
theorem paper_conclusion_godel_history_expected_liminf
    (m : ℕ) (hm : 2 ≤ m) (primes : ℕ → ℕ) (code : List ℕ)
    (hp : ∀ i, 1 < primes i)
    (hprime_lb : ∀ i, i < code.length → i + 2 ≤ primes i)
    (hcode_pos : ∀ i : Fin code.length, 1 ≤ code[i])
    (w : Omega.CircleDimension.GodelPrimeBitlengthWitness m)
    (hlen : code.length = m) :
    Nat.factorial (m + 1) ≤ godelEncoding primes 0 code ∧
      w.lowerConstant ≤ w.maxBitlength / ((m : ℝ) * Real.log (m : ℝ)) := by
  have hm1 : 1 ≤ m := by omega
  have hbit :=
    Omega.EA.paper_emergent_arithmetic_dynamic_prime_register_bitlength
      m hm1 primes code hp hprime_lb hcode_pos w
  have hfactorial : Nat.factorial (m + 1) ≤ godelEncoding primes 0 code := by
    simpa [hlen] using hbit.1
  have hm_pos : 0 < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
  have hm_gt_one : 1 < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hm)
  have hlog_mono : Real.log (m : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) := by
    exact Real.log_le_log hm_pos (by exact_mod_cast Nat.le_succ m)
  have hmain :
      w.lowerConstant * (m : ℝ) * Real.log (m : ℝ) ≤ w.maxBitlength := by
    have hcompare :
        w.lowerConstant * (m : ℝ) * Real.log (m : ℝ) ≤
          w.lowerConstant * (m : ℝ) * Real.log ((m + 1 : ℕ) : ℝ) := by
      have hscale_nonneg : 0 ≤ w.lowerConstant * (m : ℝ) := by
        have hw_nonneg : 0 ≤ w.lowerConstant := le_of_lt w.lowerConstant_pos
        nlinarith
      exact mul_le_mul_of_nonneg_left hlog_mono hscale_nonneg
    exact le_trans hcompare w.lower_bound
  have hden_pos : 0 < (m : ℝ) * Real.log (m : ℝ) := by
    have hlog_pos : 0 < Real.log (m : ℝ) := Real.log_pos hm_gt_one
    positivity
  refine ⟨hfactorial, (le_div_iff₀ hden_pos).2 ?_⟩
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmain

end Omega.Conclusion
