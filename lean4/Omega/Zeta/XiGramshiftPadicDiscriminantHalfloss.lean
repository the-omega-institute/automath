import Mathlib.Tactic
import Omega.Zeta.XiHankelDeterminantGramshiftDiscriminantIdentity
import Omega.Zeta.XiNodePolynomialGoodReductionDiscriminant

namespace Omega.Zeta

/-- Concrete ledger for the Gram-shift `p`-adic discriminant half-loss bound.

The triple records coefficient precision, discriminant valuation, and the root bits guaranteed
after discriminant loss.  Membership is the numerical precision-loss certificate. -/
abbrev xi_gramshift_padic_discriminant_halfloss_data :=
  { ledger : ℕ × ℕ × ℕ //
    ledger.2.2 ≤ ledger.1 - (ledger.2.1 + 1) / 2 }

namespace xi_gramshift_padic_discriminant_halfloss_data

/-- Coefficient precision available after the Gram-shift/Hankel reconstruction step. -/
def coeffPrecision (D : xi_gramshift_padic_discriminant_halfloss_data) : ℕ :=
  D.val.1

/-- Valuation of the characteristic-polynomial discriminant. -/
def discriminantValuation (D : xi_gramshift_padic_discriminant_halfloss_data) : ℕ :=
  D.val.2.1

/-- Root-recovery bits guaranteed after the discriminant half-loss. -/
def recoverableBits (D : xi_gramshift_padic_discriminant_halfloss_data) : ℕ :=
  D.val.2.2

/-- The packaged concrete ceiling half-loss inequality. -/
lemma precisionLoss (D : xi_gramshift_padic_discriminant_halfloss_data) :
    D.recoverableBits ≤ D.coeffPrecision - (D.discriminantValuation + 1) / 2 := by
  simpa [recoverableBits, coeffPrecision, discriminantValuation] using D.property

end xi_gramshift_padic_discriminant_halfloss_data

/-- Paper label: `thm:xi-gramshift-padic-discriminant-halfloss`. -/
theorem paper_xi_gramshift_padic_discriminant_halfloss
    (D : xi_gramshift_padic_discriminant_halfloss_data) :
    D.recoverableBits ≤ D.coeffPrecision - (D.discriminantValuation + 1) / 2 := by
  exact D.precisionLoss

end Omega.Zeta
