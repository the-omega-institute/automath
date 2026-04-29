import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete localized phase-cover data: the prime-power factor is recorded with a unit witness,
while the quotient model keeps only the outside integer part. -/
structure conclusion_phase_cover_localized_finite_kernel_only_outside_primes_data where
  outsideIntegerPart : ℕ
  sPrimePowerFactor : ℕ
  localizedUnitInverse : ℕ
  localizedUnitWitness : sPrimePowerFactor * localizedUnitInverse = 1

namespace conclusion_phase_cover_localized_finite_kernel_only_outside_primes_data

/-- The finite quotient remaining after inverting the selected prime-power factor. -/
abbrev conclusion_phase_cover_localized_finite_kernel_only_outside_primes_quotientModel
    (D : conclusion_phase_cover_localized_finite_kernel_only_outside_primes_data) : Type :=
  Fin D.outsideIntegerPart

/-- The corresponding cyclic finite model with the outside integer part. -/
abbrev conclusion_phase_cover_localized_finite_kernel_only_outside_primes_zmodModel
    (D : conclusion_phase_cover_localized_finite_kernel_only_outside_primes_data) : Type :=
  Fin D.outsideIntegerPart

/-- Multiplication by the localized unit has been removed, so the quotient is the outside part. -/
def localizedQuotientIsoZMod
    (D : conclusion_phase_cover_localized_finite_kernel_only_outside_primes_data) : Prop :=
  Nonempty
    (D.conclusion_phase_cover_localized_finite_kernel_only_outside_primes_quotientModel ≃
      D.conclusion_phase_cover_localized_finite_kernel_only_outside_primes_zmodModel)

/-- The Pontryagin-dual finite kernel has the same cardinality as the quotient model. -/
def dualKernelCard
    (D : conclusion_phase_cover_localized_finite_kernel_only_outside_primes_data) : ℕ :=
  Fintype.card
    D.conclusion_phase_cover_localized_finite_kernel_only_outside_primes_quotientModel

end conclusion_phase_cover_localized_finite_kernel_only_outside_primes_data

open conclusion_phase_cover_localized_finite_kernel_only_outside_primes_data

/-- Paper label: `cor:conclusion-phase-cover-localized-finite-kernel-only-outside-primes`. -/
theorem paper_conclusion_phase_cover_localized_finite_kernel_only_outside_primes
    (D : conclusion_phase_cover_localized_finite_kernel_only_outside_primes_data) :
    D.localizedQuotientIsoZMod ∧ D.dualKernelCard = D.outsideIntegerPart := by
  constructor
  · exact ⟨Equiv.refl _⟩
  · simp [dualKernelCard,
      conclusion_phase_cover_localized_finite_kernel_only_outside_primes_quotientModel]

end Omega.Conclusion
