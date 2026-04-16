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

/-- Paper-facing real/complex signature criterion obtained from the two circle dimensions.
    cor:conclusion-real-complex-signature-gap-criterion -/
theorem paper_conclusion_real_complex_signature_gap_criterion
    (r1 r2 a u : ℤ)
    (ha : a = r1 + 2 * r2)
    (hu : u = r1 + r2 - 1) :
    (r2 = 0 ↔ a = u + 1) ∧
    (r1 = 0 ↔ a = 2 * u + 2) ∧
    r2 = a - u - 1 := by
  rcases paper_conclusion_number_field_signature_from_two_cdims_package r1 r2 a u ha hu with
    ⟨hr2, hr1⟩
  refine ⟨?_, ?_, hr2⟩
  · rw [hr2]
    omega
  · rw [hr1]
    omega

end Omega.Conclusion.NumberFieldSignatureFromTwoCdims
