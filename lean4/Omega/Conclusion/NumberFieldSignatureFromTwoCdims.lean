import Mathlib.Tactic

namespace Omega.Conclusion.NumberFieldSignatureFromTwoCdims

/-- Paper seed: recover the Archimedean signature from the additive/unit circle-dimension pair.
    thm:conclusion-number-field-signature-from-two-cdims -/
theorem paper_conclusion_number_field_signature_from_two_cdims_seeds
    (r1 r2 a u : ℤ)
    (ha : a = r1 + 2 * r2)
    (hu : u = r1 + r2 - 1) :
    r2 = a - u - 1 ∧ r1 = 2 * u + 2 - a := by
  constructor <;> omega

/-- Packaged form of the signature recovery statement.
    thm:conclusion-number-field-signature-from-two-cdims -/
theorem paper_conclusion_number_field_signature_from_two_cdims_package
    (r1 r2 a u : ℤ)
    (ha : a = r1 + 2 * r2)
    (hu : u = r1 + r2 - 1) :
    r2 = a - u - 1 ∧ r1 = 2 * u + 2 - a :=
  paper_conclusion_number_field_signature_from_two_cdims_seeds r1 r2 a u ha hu

end Omega.Conclusion.NumberFieldSignatureFromTwoCdims
