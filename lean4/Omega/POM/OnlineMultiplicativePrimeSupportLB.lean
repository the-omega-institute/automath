import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- A concrete logarithmic lower bound for the number of support primes in an online multiplicative
encoding.  The hypothesis is the image-size estimate produced by the valuation-vector argument in
the paper.  This avoids introducing a new abstract `...Data` shell while keeping the lower-bound
conclusion in the paper-facing form.  `thm:pom-online-multiplicative-prime-support-lb` -/
theorem paper_pom_online_multiplicative_prime_support_lb
    (A T : ℕ) (kappa : ℝ) (support : Finset ℕ) (hA : 2 ≤ A) (hkappa : 0 ≤ kappa)
    (hcard :
      (A : ℝ) ^ T ≤
        (1 + kappa / Real.log 2 * Real.log (Nat.factorial T)) ^ support.card) :
    ((T : ℝ) * Real.log A /
        Real.log (1 + kappa / Real.log 2 * Real.log (Nat.factorial T)) ≤ support.card) := by
  let B : ℝ := 1 + kappa / Real.log 2 * Real.log (Nat.factorial T)
  have hAposNat : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hApos : 0 < (A : ℝ) := by exact_mod_cast hAposNat
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfac : 1 ≤ (Nat.factorial T : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos T)
  have hB_ge_one : 1 ≤ B := by
    have hkdiv : 0 ≤ kappa / Real.log 2 := div_nonneg hkappa hlog2.le
    have hfaclog : 0 ≤ Real.log (Nat.factorial T : ℝ) := Real.log_nonneg hfac
    have hprod : 0 ≤ kappa / Real.log 2 * Real.log (Nat.factorial T : ℝ) :=
      mul_nonneg hkdiv hfaclog
    dsimp [B]
    linarith
  have hlogB_nonneg : 0 ≤ Real.log B := Real.log_nonneg hB_ge_one
  have hlogineq : Real.log ((A : ℝ) ^ T) ≤ Real.log (B ^ support.card) := by
    simpa [B] using Real.log_le_log (pow_pos hApos T) hcard
  rw [Real.log_pow, Real.log_pow] at hlogineq
  by_cases hlogB : Real.log B = 0
  · simp [B, hlogB]
  · have hlogBne0 : 0 ≠ Real.log B := by simpa [eq_comm] using hlogB
    have hlogB_pos : 0 < Real.log B := lt_of_le_of_ne hlogB_nonneg hlogBne0
    rw [div_le_iff₀ hlogB_pos]
    simpa [B, mul_comm, mul_left_comm, mul_assoc] using hlogineq

end Omega.POM
