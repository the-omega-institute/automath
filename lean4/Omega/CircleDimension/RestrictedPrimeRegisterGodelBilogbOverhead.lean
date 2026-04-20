import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.CircleDimension.GodelPrimeBitlengthLowerBound
import Omega.CircleDimension.PrefixPrimeLedgerConservation

namespace Omega.CircleDimension

/-- Witness packaging a `B`-ary coding lower bound on the required code length together with the
existing prime-register bitlength lower bound applied to that code length. -/
structure RestrictedPrimeRegisterGodelBilogbWitness (r k B : ℕ) where
  additiveSlack : ℝ
  codeLength : ℕ → ℕ
  codeLength_pos : ∀ b : ℕ, 1 ≤ codeLength b
  codeLength_lower :
    ∀ b : ℕ, (((r - k) * b : ℝ) / realLog2 (B : ℝ)) - additiveSlack ≤ (codeLength b : ℝ)
  godelWitness : ∀ b : ℕ, GodelPrimeBitlengthWitness (codeLength b)

/-- Paper-facing overhead package: the `B`-ary injective code forces a linear-in-`b` lower bound
on the required prime-register length, and the existing Gödel bitlength theorem turns that into a
`T_b log T_b` lower bound for the compressed integer. -/
def RestrictedPrimeRegisterGodelBilogbOverhead {r k B : ℕ}
    (w : RestrictedPrimeRegisterGodelBilogbWitness r k B) : Prop :=
  (∀ b : ℕ, (((r - k) * b : ℝ) / realLog2 (B : ℝ)) - w.additiveSlack ≤ (w.codeLength b : ℝ)) ∧
    ∀ b : ℕ, ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      c * (w.codeLength b : ℝ) * Real.log (((w.codeLength b + 1 : ℕ) : ℝ)) ≤
        (w.godelWitness b).maxBitlength ∧
      (w.godelWitness b).maxBitlength ≤
        C * (w.codeLength b : ℝ) * Real.log (((w.codeLength b + 1 : ℕ) : ℝ))

/-- Packaging the residual-cardinality/code-length lower bound with the existing prime-register
bitlength theorem yields the advertised `b log b`-style overhead interface.
    thm:cdim-restricted-prime-register-godel-bilogb-overhead -/
theorem paper_cdim_restricted_prime_register_godel_bilogb_overhead
    (r k B : ℕ) (hB : 2 ≤ B) (w : RestrictedPrimeRegisterGodelBilogbWitness r k B) :
    RestrictedPrimeRegisterGodelBilogbOverhead w := by
  let _ := hB
  refine ⟨w.codeLength_lower, ?_⟩
  intro b
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    paper_cdim_godel_prime_bitlength_lowerbound (w.codeLength b) 1 (w.codeLength_pos b) (by decide)
      (w.godelWitness b)

end Omega.CircleDimension
