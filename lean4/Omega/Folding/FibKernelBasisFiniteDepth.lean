import Mathlib.Data.Finsupp.SMul
import Mathlib.Tactic
import Omega.EA.PrimeRegisterResidualLedgerGroup

namespace Omega.Folding

open Omega.EA

/-- Every residual Fibonacci generator lies in the zero-ledger kernel. -/
private theorem residualBasisGenerator_mem_kernel (k : ℕ) :
    ledgerValZ (residualBasisGenerator k) = 0 := by
  cases k with
  | zero =>
      exact Omega.EA.paper_prime_register_residual_ledger_group.1
  | succ k =>
      exact Omega.EA.paper_prime_register_residual_ledger_group.2.1 k

/-- The `k`-th residual Fibonacci generator is supported on coordinates at most `k + 2`. -/
private theorem residualBasisGenerator_support_bound (k j : ℕ) (hj : k + 2 < j) :
    residualBasisGenerator k j = 0 := by
  cases k with
  | zero =>
      simp [Omega.EA.residualBasisGenerator, Finsupp.single_apply]
      omega
  | succ k =>
      simp [Omega.EA.residualBasisGenerator, Finsupp.single_apply]
      omega

/-- Matching normalized prime register and residual factor determine the original exponent
vector uniquely. -/
private theorem theta_eq_of_nfpr_and_residual_eq {a b : DigitCfg}
    (hNF : NF_pr a = NF_pr b) (hR : R a = R b) : Theta a = Theta b := by
  unfold Theta
  refine Prod.ext ?_ hR
  exact Subtype.ext hNF

/-- Finite-depth wrapper for the Fibonacci valuation kernel: every listed generator lies in the
kernel, each generator is supported within its advertised depth window, and the transported
prime-register decomposition `(NF_pr, R)` is unique.
    thm:fib-kernel-basis-finite-depth -/
theorem paper_fib_kernel_basis_finite_depth (L : ℕ) :
    (∀ k, k < L → ledgerValZ (residualBasisGenerator k) = 0) ∧
    (∀ k, k < L → ∀ j, k + 2 < j → residualBasisGenerator k j = 0) ∧
      Function.Injective Theta ∧
      (∀ a b : DigitCfg, NF_pr a = NF_pr b → R a = R b → a = b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k _hk
    exact residualBasisGenerator_mem_kernel k
  · intro k _hk j hj
    exact residualBasisGenerator_support_bound k j hj
  · exact Omega.EA.paper_prime_register_residual_ledger_group.2.2.2.2
  · intro a b hNF hR
    have hTheta : Theta a = Theta b := theta_eq_of_nfpr_and_residual_eq hNF hR
    exact Omega.EA.paper_prime_register_residual_ledger_group.2.2.2.2 hTheta

end Omega.Folding
