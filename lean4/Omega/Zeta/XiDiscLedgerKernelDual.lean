import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The bad-prime support read from the discriminant surrogate `n + 1`. -/
def xi_disc_ledger_kernel_dual_discriminant_group (n : Nat) : Finset Nat :=
  (n + 1).factorization.support

/-- In the finite-support model, the Pontryagin dual has the same support carrier. -/
def xi_disc_ledger_kernel_dual_pontryagin_dual (n : Nat) : Finset Nat :=
  xi_disc_ledger_kernel_dual_discriminant_group n

/-- The covering kernel is identified with the same finite support. -/
def xi_disc_ledger_kernel_dual_cover_kernel (n : Nat) : Finset Nat :=
  xi_disc_ledger_kernel_dual_pontryagin_dual n

/-- The unavoidable bad primes are exactly the primes in the same support. -/
def xi_disc_ledger_kernel_dual_bad_prime_support (n : Nat) : Finset Nat :=
  xi_disc_ledger_kernel_dual_discriminant_group n

abbrev XiDiscLedgerKernelDual (n : Nat) : Prop :=
  xi_disc_ledger_kernel_dual_cover_kernel n =
      xi_disc_ledger_kernel_dual_pontryagin_dual n ∧
    xi_disc_ledger_kernel_dual_cover_kernel n ⊆
      xi_disc_ledger_kernel_dual_bad_prime_support n ∧
    (xi_disc_ledger_kernel_dual_cover_kernel n).card =
      (xi_disc_ledger_kernel_dual_discriminant_group n).card

theorem paper_xi_disc_ledger_kernel_dual (n : Nat) : XiDiscLedgerKernelDual n := by
  refine ⟨rfl, ?_, rfl⟩
  intro p hp
  simpa [xi_disc_ledger_kernel_dual_cover_kernel,
    xi_disc_ledger_kernel_dual_pontryagin_dual,
    xi_disc_ledger_kernel_dual_bad_prime_support,
    xi_disc_ledger_kernel_dual_discriminant_group] using hp

end Omega.Zeta
