import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete cover-kernel signature package.  The kernel support is the finite set of detected
kernel primes; the ambient ledger support adjoins the declared auxiliary prime support. -/
structure conclusion_cover_kernel_min_prime_ledger_signature_Data where
  conclusion_cover_kernel_min_prime_ledger_signature_kernelSupport : Finset ℕ
  conclusion_cover_kernel_min_prime_ledger_signature_declaredPrimeSupport : Finset ℕ

namespace conclusion_cover_kernel_min_prime_ledger_signature_Data

/-- The finite ledger support containing the cover kernel and any declared auxiliary primes. -/
def conclusion_cover_kernel_min_prime_ledger_signature_ledgerSupport
    (D : conclusion_cover_kernel_min_prime_ledger_signature_Data) : Finset ℕ :=
  D.conclusion_cover_kernel_min_prime_ledger_signature_kernelSupport ∪
    D.conclusion_cover_kernel_min_prime_ledger_signature_declaredPrimeSupport

/-- The kernel embeds into the ledger through the left inclusion into the union support. -/
def conclusion_cover_kernel_min_prime_ledger_signature_kernelEmbeds
    (D : conclusion_cover_kernel_min_prime_ledger_signature_Data) : Prop :=
  D.conclusion_cover_kernel_min_prime_ledger_signature_kernelSupport ⊆
    D.conclusion_cover_kernel_min_prime_ledger_signature_ledgerSupport

/-- Any finite ledger containing the kernel has cardinality at least the kernel support. -/
def conclusion_cover_kernel_min_prime_ledger_signature_finiteLedgerCardLowerBound
    (D : conclusion_cover_kernel_min_prime_ledger_signature_Data) : Prop :=
  D.conclusion_cover_kernel_min_prime_ledger_signature_kernelSupport.card ≤
    D.conclusion_cover_kernel_min_prime_ledger_signature_ledgerSupport.card

/-- Every kernel prime is necessarily present in the prime ledger support. -/
def conclusion_cover_kernel_min_prime_ledger_signature_primeSupportNecessary
    (D : conclusion_cover_kernel_min_prime_ledger_signature_Data) : Prop :=
  ∀ p ∈ D.conclusion_cover_kernel_min_prime_ledger_signature_kernelSupport,
    p ∈ D.conclusion_cover_kernel_min_prime_ledger_signature_ledgerSupport

end conclusion_cover_kernel_min_prime_ledger_signature_Data

open conclusion_cover_kernel_min_prime_ledger_signature_Data

/-- Paper label: `thm:conclusion-cover-kernel-min-prime-ledger-signature`. -/
theorem paper_conclusion_cover_kernel_min_prime_ledger_signature
    (D : conclusion_cover_kernel_min_prime_ledger_signature_Data) :
    D.conclusion_cover_kernel_min_prime_ledger_signature_kernelEmbeds ∧
      D.conclusion_cover_kernel_min_prime_ledger_signature_finiteLedgerCardLowerBound ∧
        D.conclusion_cover_kernel_min_prime_ledger_signature_primeSupportNecessary := by
  have hsubset : D.conclusion_cover_kernel_min_prime_ledger_signature_kernelSupport ⊆
      D.conclusion_cover_kernel_min_prime_ledger_signature_ledgerSupport := by
    intro p hp
    exact Finset.mem_union_left
      D.conclusion_cover_kernel_min_prime_ledger_signature_declaredPrimeSupport hp
  refine ⟨hsubset, ?_, ?_⟩
  · exact Finset.card_le_card hsubset
  · intro p hp
    exact hsubset hp

end Omega.Conclusion
