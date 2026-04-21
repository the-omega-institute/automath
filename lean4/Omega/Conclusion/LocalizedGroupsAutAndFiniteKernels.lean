import Mathlib.Tactic
import Omega.Zeta.LocalizedIntegersEndomorphismAutomorphismExplicit
import Omega.Zeta.LocalizedUnitAutomorphismGroupClassification
import Omega.Zeta.LocalizedSolenoidCircleQuotientLifts

namespace Omega.Conclusion

open Omega.Zeta

/-- Concrete localization data: a finite prime set `S`, one supported scalar, one explicit unit
coordinate, and a prime modulus outside `S` for the finite-kernel package. -/
structure LocalizedGroupsAutAndFiniteKernelsData where
  S : FinitePrimeLocalization
  scalar : SupportedLocalizedIntegerGroup S
  unitCoordinates : LocalizedUnitCoordinates S
  m : ℕ
  hm_prime : m.Prime
  hm_not_mem : m ∉ S

namespace LocalizedGroupsAutAndFiniteKernelsData

/-- A localized scalar acts by the additive endomorphism determined by the image of `1`. -/
def endRingFormula (D : LocalizedGroupsAutAndFiniteKernelsData) : Prop :=
  ∃ φ : SupportedLocalizedIntegerGroup D.S →+ SupportedLocalizedIntegerGroup D.S,
    ∀ x : SupportedLocalizedIntegerGroup D.S, (φ x : ℚ) = D.scalar.1 * x.1

/-- The unit group is represented by the explicit signed prime-power coordinate model. -/
def unitGroupFormula (D : LocalizedGroupsAutAndFiniteKernelsData) : Prop :=
  denominatorSupportedBy D.S (localizedUnitScalar D.S D.unitCoordinates) ∧
    localizedUnitScalar D.S D.unitCoordinates ≠ 0 ∧
    denominatorSupportedBy D.S (localizedUnitScalar D.S D.unitCoordinates)⁻¹ ∧
    ∃ σ : SupportedLocalizedIntegerGroup D.S ≃+ SupportedLocalizedIntegerGroup D.S,
      ∀ x : SupportedLocalizedIntegerGroup D.S,
        (σ x : ℚ) = localizedUnitScalar D.S D.unitCoordinates * x.1

/-- For a prime modulus outside the localization support, the finite quotient retains size `m`. -/
def quotientFormula (D : LocalizedGroupsAutAndFiniteKernelsData) : Prop :=
  localizedIndex D.S D.m = D.m

/-- On the dual side, the corresponding finite kernel has cardinality `m`. -/
def dualKernelCardinality (D : LocalizedGroupsAutAndFiniteKernelsData) : Prop :=
  0 < localizedIndex D.S D.m ∧ localizedIndex D.S D.m = D.m

end LocalizedGroupsAutAndFiniteKernelsData

open LocalizedGroupsAutAndFiniteKernelsData

/-- Paper label: `thm:conclusion-localized-groups-aut-and-finite-kernels`. -/
theorem paper_conclusion_localized_groups_aut_and_finite_kernels
    (D : LocalizedGroupsAutAndFiniteKernelsData) :
    D.endRingFormula ∧ D.unitGroupFormula ∧ D.quotientFormula ∧ D.dualKernelCardinality := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases (paper_xi_localized_integers_endomorphism_automorphism_explicit D.S).1 D.scalar with
      ⟨φ, hφ⟩
    exact ⟨φ, hφ⟩
  · exact (paper_xi_time_part69_localized_unit_automorphism_group_classification D.S).1
      D.unitCoordinates
  · exact (paper_xi_time_part62db_localized_solenoid_circle_quotient_lifts D.S D.m D.hm_prime).2.2
      |>.1 D.hm_not_mem
  · have hq : localizedIndex D.S D.m = D.m :=
      (paper_xi_time_part62db_localized_solenoid_circle_quotient_lifts D.S D.m D.hm_prime).2.2
        |>.1 D.hm_not_mem
    refine ⟨?_, hq⟩
    simpa [hq] using D.hm_prime.pos

end Omega.Conclusion
