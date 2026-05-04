import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Paper label: `prop:xi-ihara-zk-soundness-exponent`. -/
theorem paper_xi_ihara_zk_soundness_exponent (passProb : ℕ → ℝ) (c lambdaP d lambdaA : ℝ)
    (hlambdaP_nonneg : 0 ≤ lambdaP) (h0 : passProb 0 ≤ c)
    (hstep : ∀ n, passProb (n + 1) ≤ lambdaP * passProb n)
    (hlambdaP_eq : lambdaP = lambdaA / d) :
    (∀ n, passProb n ≤ c * lambdaP ^ n) ∧ lambdaP = lambdaA / d := by
  refine ⟨?_, hlambdaP_eq⟩
  intro n
  induction n with
  | zero =>
      simpa using h0
  | succ n ih =>
      calc
        passProb (n + 1) ≤ lambdaP * passProb n := hstep n
        _ ≤ lambdaP * (c * lambdaP ^ n) := mul_le_mul_of_nonneg_left ih hlambdaP_nonneg
        _ = c * lambdaP ^ (n + 1) := by
          rw [pow_succ]
          ring

end Omega.SyncKernelWeighted
