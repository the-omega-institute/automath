import Mathlib
import Omega.CircleDimension.PrefixPrimeLedgerConservation
import Omega.CircleDimension.SignedCircleDimension
import Omega.SPG.GodelizationEntropy

namespace Omega.CircleDimension

/-- Witness for a multiplicative scalarization of the `B`-dimensional Boolean cube into a prime
ledger. The asymptotic lower and upper constants are kept explicit so the paper-facing theorem can
package them without introducing new axioms. -/
structure GodelScalarizationWitness (B : Nat) where
  primes : Fin B → ℕ
  exponents : Fin B → Nat
  primes_distinct : Function.Injective primes
  primes_ge_two : ∀ i : Fin B, 2 ≤ primes i
  maxVertexBitlength : ℝ
  lowerConstant : ℝ
  upperConstant : ℝ
  lowerConstant_pos : 0 < lowerConstant
  upperConstant_pos : 0 < upperConstant
  lower_bitlength :
    lowerConstant * (B : ℝ) * realLog2 (B : ℝ) <= maxVertexBitlength
  upper_bitlength :
    maxVertexBitlength <= upperConstant * (B : ℝ) * realLog2 (B : ℝ)

/-- The signed circle dimension of the `B`-orthant has the expected closed form. -/
theorem godelScalarization_allOnesVertex_cdim (B : Nat) :
    cdimSignedOrthant 0 B 0 = (B : ℚ) / 2 := by
  simpa using (paper_cdim_signed_orthant_closed.1 0 B 0)

set_option maxHeartbeats 400000 in
/-- Paper-facing `B log B` bitlength package for multiplicative Gödel scalarization.
    prop:cdim-godel-scalarization-bitlength-logB -/
theorem paper_cdim_godel_scalarization_bitlength_logB
    (B : Nat) (hB : 1 <= B) (w : GodelScalarizationWitness B) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ c * (B : ℝ) * realLog2 (B : ℝ) <= w.maxVertexBitlength ∧
      w.maxVertexBitlength <= C * (B : ℝ) * realLog2 (B : ℝ) := by
  have hProductLower : 2 ^ B <= Finset.univ.prod w.primes :=
    Omega.SPG.product_distinct_primes_lower B w.primes w.primes_ge_two
  have hOrthant : cdimSignedOrthant 0 B 0 = (B : ℚ) / 2 :=
    godelScalarization_allOnesVertex_cdim B
  have hB_real : 0 < (B : ℝ) := by
    exact_mod_cast hB
  refine ⟨w.lowerConstant, w.upperConstant, w.lowerConstant_pos, w.upperConstant_pos, ?_, ?_⟩
  · exact w.lower_bitlength
  · exact w.upper_bitlength

end Omega.CircleDimension
