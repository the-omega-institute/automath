import Mathlib.Tactic

namespace Omega.Conclusion

universe u

/-- Concrete fixed-prime zero-law data for the certificate obstruction. -/
structure conclusion_asymptotic_zero_law_certificate_cannot_recover_fixed_prime_data where
  limitLaw : Type u
  fixedPrime : ℕ
  leftLedger : ℕ → ℤ
  rightLedger : ℕ → ℤ
  leftZeroLaw : limitLaw
  rightZeroLaw : limitLaw
  sharedZeroLaw : limitLaw
  left_converges_to_shared : leftZeroLaw = sharedZeroLaw
  right_converges_to_shared : rightZeroLaw = sharedZeroLaw
  fixed_prime_distinguishable : leftLedger fixedPrime ≠ rightLedger fixedPrime

namespace conclusion_asymptotic_zero_law_certificate_cannot_recover_fixed_prime_data

/-- No readout depending only on the limiting zero law can recover both fixed-prime values. -/
def no_certificate
    (D : conclusion_asymptotic_zero_law_certificate_cannot_recover_fixed_prime_data) :
    Prop :=
  ¬ ∃ certificate : D.limitLaw → ℤ,
    certificate D.leftZeroLaw = D.leftLedger D.fixedPrime ∧
      certificate D.rightZeroLaw = D.rightLedger D.fixedPrime

end conclusion_asymptotic_zero_law_certificate_cannot_recover_fixed_prime_data

/-- Paper label: `cor:conclusion-asymptotic-zero-law-certificate-cannot-recover-fixed-prime`. -/
theorem paper_conclusion_asymptotic_zero_law_certificate_cannot_recover_fixed_prime
    (D : conclusion_asymptotic_zero_law_certificate_cannot_recover_fixed_prime_data) :
    D.no_certificate := by
  rintro ⟨certificate, hleft, hright⟩
  have hsameLaw : D.leftZeroLaw = D.rightZeroLaw := by
    rw [D.left_converges_to_shared, D.right_converges_to_shared]
  apply D.fixed_prime_distinguishable
  calc
    D.leftLedger D.fixedPrime = certificate D.leftZeroLaw := hleft.symm
    _ = certificate D.rightZeroLaw := by rw [hsameLaw]
    _ = D.rightLedger D.fixedPrime := hright

end Omega.Conclusion
