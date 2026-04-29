import Mathlib.Tactic
import Omega.Conclusion.ZGFiniteCertificateFiberFullSpectrum

namespace Omega.Conclusion

/-- The finite certificate atom selected by a cylinder and a finite prime-shadow value. -/
def conclusion_zg_finite_certificate_local_dimension_blindness_atom
    {Source Base Solenoid Shadow : Type} (cylinder : Source → Prop) (map : Source → Base)
    (projection : Solenoid → Shadow) (eta : Shadow) (p : Base × Solenoid) : Prop :=
  conclusion_zg_finite_certificate_fiber_full_spectrum_in_finite_certificate_fiber
    cylinder map projection eta p

/-- Constancy of a local-dimension readout on one finite certificate atom. -/
def conclusion_zg_finite_certificate_local_dimension_blindness_constant_on_atom
    {Source Base Solenoid Shadow : Type} (cylinder : Source → Prop) (map : Source → Base)
    (projection : Solenoid → Shadow) (eta : Shadow) (localDimension : Base → ℝ) : Prop :=
  ∃ c : ℝ, ∀ p : Base × Solenoid,
    conclusion_zg_finite_certificate_local_dimension_blindness_atom
      cylinder map projection eta p →
        localDimension p.1 = c

/-- Concrete package: full local-dimension spectrum on a finite certificate atom rules out
constancy, hence finite-certificate local-dimension readability. -/
def conclusion_zg_finite_certificate_local_dimension_blindness_statement : Prop :=
  ∀ {Source Base Solenoid Shadow : Type} (cylinder : Source → Prop) (map : Source → Base)
    (projection : Solenoid → Shadow) (eta : Shadow) (localDimension : Base → ℝ),
      (∀ α : ℝ, ∃ z, cylinder z ∧ localDimension (map z) = α) →
        (∃ xi, projection xi = eta) →
          (∀ α : ℝ, ∃ p : Base × Solenoid,
            conclusion_zg_finite_certificate_local_dimension_blindness_atom
                cylinder map projection eta p ∧
              localDimension p.1 = α) ∧
            ¬ conclusion_zg_finite_certificate_local_dimension_blindness_constant_on_atom
              cylinder map projection eta localDimension

/-- Paper label: `thm:conclusion-zg-finite-certificate-local-dimension-blindness`. -/
theorem paper_conclusion_zg_finite_certificate_local_dimension_blindness :
    conclusion_zg_finite_certificate_local_dimension_blindness_statement := by
  intro Source Base Solenoid Shadow cylinder map projection eta localDimension
    fullSpectrumInCylinder projectionSurjectiveAtEta
  have hfull :
      ∀ α : ℝ, ∃ p : Base × Solenoid,
        conclusion_zg_finite_certificate_local_dimension_blindness_atom
            cylinder map projection eta p ∧
          localDimension p.1 = α := by
    simpa [conclusion_zg_finite_certificate_local_dimension_blindness_atom] using
      paper_conclusion_zg_finite_certificate_fiber_full_spectrum cylinder map projection eta
        localDimension fullSpectrumInCylinder projectionSurjectiveAtEta
  refine ⟨hfull, ?_⟩
  intro hconstant
  rcases hconstant with ⟨c, hc⟩
  rcases hfull (c + 1) with ⟨p, hpatom, hpdim⟩
  have hpconst : localDimension p.1 = c := hc p hpatom
  linarith

end Omega.Conclusion
