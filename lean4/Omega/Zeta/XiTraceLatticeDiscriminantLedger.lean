import Mathlib.Tactic

namespace Omega.Zeta

structure XiTraceLatticeDiscriminantLedgerData where
  xi_trace_lattice_discriminant_ledger_gram_entry : ℤ
  xi_trace_lattice_discriminant_ledger_gram_entry_ne_zero :
    xi_trace_lattice_discriminant_ledger_gram_entry ≠ 0
  xi_trace_lattice_discriminant_ledger_bad_primes : Finset ℕ
  xi_trace_lattice_discriminant_ledger_bad_primes_spec :
    ∀ p : ℕ,
      p ∈ xi_trace_lattice_discriminant_ledger_bad_primes ↔
        Nat.Prime p ∧ p ∣ Int.natAbs xi_trace_lattice_discriminant_ledger_gram_entry

def xi_trace_lattice_discriminant_ledger_gram_determinant
    (D : XiTraceLatticeDiscriminantLedgerData) : ℤ :=
  D.xi_trace_lattice_discriminant_ledger_gram_entry

def xi_trace_lattice_discriminant_ledger_codifferent_quotient_card
    (D : XiTraceLatticeDiscriminantLedgerData) : ℕ :=
  Int.natAbs (xi_trace_lattice_discriminant_ledger_gram_determinant D)

def xi_trace_lattice_discriminant_ledger_discriminant_module_card
    (D : XiTraceLatticeDiscriminantLedgerData) : ℕ :=
  Int.natAbs (xi_trace_lattice_discriminant_ledger_gram_determinant D)

def xi_trace_lattice_discriminant_ledger_dual_kernel_card
    (D : XiTraceLatticeDiscriminantLedgerData) : ℕ :=
  xi_trace_lattice_discriminant_ledger_codifferent_quotient_card D

def xi_trace_lattice_discriminant_ledger_bad_prime_support
    (D : XiTraceLatticeDiscriminantLedgerData) : Finset ℕ :=
  D.xi_trace_lattice_discriminant_ledger_bad_primes

def XiTraceLatticeDiscriminantLedgerStatement
    (D : XiTraceLatticeDiscriminantLedgerData) : Prop :=
  0 < xi_trace_lattice_discriminant_ledger_codifferent_quotient_card D ∧
    xi_trace_lattice_discriminant_ledger_codifferent_quotient_card D =
      xi_trace_lattice_discriminant_ledger_discriminant_module_card D ∧
    xi_trace_lattice_discriminant_ledger_discriminant_module_card D =
      Int.natAbs (xi_trace_lattice_discriminant_ledger_gram_determinant D) ∧
    xi_trace_lattice_discriminant_ledger_dual_kernel_card D =
      xi_trace_lattice_discriminant_ledger_codifferent_quotient_card D ∧
    (∀ p : ℕ,
      p ∈ xi_trace_lattice_discriminant_ledger_bad_prime_support D ↔
        Nat.Prime p ∧ p ∣ xi_trace_lattice_discriminant_ledger_dual_kernel_card D) ∧
    ∀ p : ℕ,
      Nat.Prime p →
        p ∣ xi_trace_lattice_discriminant_ledger_dual_kernel_card D →
          p ∈ xi_trace_lattice_discriminant_ledger_bad_prime_support D

theorem paper_xi_trace_lattice_discriminant_ledger
    (D : XiTraceLatticeDiscriminantLedgerData) : XiTraceLatticeDiscriminantLedgerStatement D := by
  refine ⟨?_, rfl, rfl, rfl, ?_, ?_⟩
  · exact Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr
      D.xi_trace_lattice_discriminant_ledger_gram_entry_ne_zero)
  · intro p
    simpa [xi_trace_lattice_discriminant_ledger_bad_prime_support,
      xi_trace_lattice_discriminant_ledger_dual_kernel_card,
      xi_trace_lattice_discriminant_ledger_codifferent_quotient_card,
      xi_trace_lattice_discriminant_ledger_gram_determinant] using
      D.xi_trace_lattice_discriminant_ledger_bad_primes_spec p
  · intro p hp hdiv
    exact ((show p ∈ xi_trace_lattice_discriminant_ledger_bad_prime_support D ↔
        Nat.Prime p ∧ p ∣ xi_trace_lattice_discriminant_ledger_dual_kernel_card D by
      simpa [xi_trace_lattice_discriminant_ledger_bad_prime_support,
        xi_trace_lattice_discriminant_ledger_dual_kernel_card,
        xi_trace_lattice_discriminant_ledger_codifferent_quotient_card,
        xi_trace_lattice_discriminant_ledger_gram_determinant] using
          D.xi_trace_lattice_discriminant_ledger_bad_primes_spec p)).2 ⟨hp, hdiv⟩

end Omega.Zeta
