import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Nat.Factorization.Basic

namespace Omega.EA

/-- The finite visible ledger: keep only the prime-factor exponents indexed by `S`. -/
def primeRegisterFiniteLedger (S : Finset Nat) (n : Nat) : Nat →₀ Nat :=
  n.factorization.filter fun p => p ∈ S

/-- The visible multiplicative part reconstructed from the truncated ledger. -/
def primeRegisterVisiblePart (S : Finset Nat) (n : Nat) : Nat :=
  (primeRegisterFiniteLedger S n).prod (· ^ ·)

/-- The residual cofactor outside the visible ledger window. We record `0` separately so that the
reconstruction formula holds uniformly for all naturals. -/
def primeRegisterResidualCofactor (S : Finset Nat) (n : Nat) : Nat :=
  if n = 0 then 0 else (n.factorization.filter fun p => p ∉ S).prod (· ^ ·)

theorem primeRegisterFiniteLedger_reconstruction (S : Finset Nat) (n : Nat) :
    n = primeRegisterVisiblePart S n * primeRegisterResidualCofactor S n := by
  by_cases hn : n = 0
  · simp [primeRegisterVisiblePart, primeRegisterFiniteLedger, primeRegisterResidualCofactor, hn]
  · calc
      n = n.factorization.prod (· ^ ·) := by
        symm
        exact Nat.factorization_prod_pow_eq_self hn
      _ = (n.factorization.filter fun p => p ∈ S).prod (· ^ ·) *
          (n.factorization.filter fun p => p ∉ S).prod (· ^ ·) := by
        symm
        exact Finsupp.prod_filter_mul_prod_filter_not
          (f := n.factorization) (p := fun p => p ∈ S) (g := fun p k => p ^ k)
      _ = primeRegisterVisiblePart S n * primeRegisterResidualCofactor S n := by
        simp [primeRegisterVisiblePart, primeRegisterFiniteLedger, primeRegisterResidualCofactor, hn]

/-- Paper-facing wrapper: a finite visible ledger together with the residual cofactor uniquely
reconstructs the original natural number.
prop:prime-register-finite-ledger-recoverability -/
theorem paper_prime_register_finite_ledger_recoverability (S : Finset Nat) :
    Function.Injective
      (fun n : Nat => (primeRegisterFiniteLedger S n, primeRegisterResidualCofactor S n)) := by
  intro a b h
  have hLedger : primeRegisterFiniteLedger S a = primeRegisterFiniteLedger S b :=
    congrArg Prod.fst h
  have hResidual : primeRegisterResidualCofactor S a = primeRegisterResidualCofactor S b :=
    congrArg Prod.snd h
  calc
    a = primeRegisterVisiblePart S a * primeRegisterResidualCofactor S a := by
      exact primeRegisterFiniteLedger_reconstruction S a
    _ = primeRegisterVisiblePart S b * primeRegisterResidualCofactor S b := by
      simp [primeRegisterVisiblePart, hLedger, hResidual]
    _ = b := by
      exact (primeRegisterFiniteLedger_reconstruction S b).symm

end Omega.EA
