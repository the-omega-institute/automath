import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic
import Omega.Zeta.LocalizedIntegersEndomorphismAutomorphismExplicit

namespace Omega.CircleDimension

open Omega.Zeta

/-- The finite prime witness extracted from a finite family of rational frequencies:
    collect every prime dividing a reduced denominator. -/
noncomputable def qhatPrimeWitnessSet (Q : Finset ℚ) : Finset ℕ :=
  Q.biUnion fun q => q.den.primeFactors

/-- Every frequency in `Q` already factors through the stage indexed by the witness set built from
    the denominator prime factors of `Q`. -/
lemma denominatorSupportedBy_qhatPrimeWitnessSet (Q : Finset ℚ) {q : ℚ} (hq : q ∈ Q) :
    denominatorSupportedBy (qhatPrimeWitnessSet Q) q := by
  intro p hp hdiv
  exact Finset.mem_biUnion.mpr
    ⟨q, hq, Nat.mem_primeFactors.mpr ⟨hp, hdiv, q.den_ne_zero⟩⟩

/-- A finite trigonometric certificate is represented concretely by an integer coefficient function
    with finite rational support. Factoring through a finite prime stage means every frequency with
    nonzero coefficient has `S`-supported denominator. -/
def qhatCertificateFactorsThrough (S : Finset ℕ) (coeff : ℚ → ℤ) : Prop :=
  ∀ q, coeff q ≠ 0 → denominatorSupportedBy S q

/-- A finite family of rational frequencies admits a finite prime witness set, obtained by taking
    the union of all denominator prime factors. Every individual character and every finite
    trigonometric certificate supported on that family then factors through the same finite stage.
    thm:cdim-qhat-finite-prime-witness -/
theorem paper_cdim_qhat_finite_prime_witness (Q : Finset ℚ) :
    ∃ S : Finset ℕ,
      (∀ q ∈ Q, denominatorSupportedBy S q) ∧
      ∀ coeff : ℚ → ℤ, (∀ q, coeff q ≠ 0 → q ∈ Q) → qhatCertificateFactorsThrough S coeff := by
  refine ⟨qhatPrimeWitnessSet Q, ?_, ?_⟩
  · intro q hq
    exact denominatorSupportedBy_qhatPrimeWitnessSet Q hq
  · intro coeff hcoeff q hqcoeff
    exact denominatorSupportedBy_qhatPrimeWitnessSet Q (hcoeff q hqcoeff)

end Omega.CircleDimension
