import Mathlib.Tactic

namespace Omega.Conclusion

/-- The finite certificate fiber over a chosen cylinder and finite prime shadow. -/
def conclusion_zg_finite_certificate_fiber_full_spectrum_in_finite_certificate_fiber
    {Source Base Solenoid Shadow : Type} (cylinder : Source → Prop) (map : Source → Base)
    (projection : Solenoid → Shadow) (eta : Shadow) (p : Base × Solenoid) : Prop :=
  ∃ z, cylinder z ∧ p.1 = map z ∧ projection p.2 = eta

/-- Paper label: `thm:conclusion-zg-finite-certificate-fiber-full-spectrum`. -/
theorem paper_conclusion_zg_finite_certificate_fiber_full_spectrum
    {Source Base Solenoid Shadow : Type} (cylinder : Source → Prop) (map : Source → Base)
    (projection : Solenoid → Shadow) (eta : Shadow) (localDimension : Base → ℝ)
    (fullSpectrumInCylinder : ∀ α : ℝ, ∃ z, cylinder z ∧ localDimension (map z) = α)
    (projectionSurjectiveAtEta : ∃ xi, projection xi = eta) :
    ∀ α : ℝ,
      ∃ p : Base × Solenoid,
        conclusion_zg_finite_certificate_fiber_full_spectrum_in_finite_certificate_fiber
            cylinder map projection eta p ∧
          localDimension p.1 = α := by
  intro α
  obtain ⟨z, hzC, hzdim⟩ := fullSpectrumInCylinder α
  obtain ⟨xi, hxi⟩ := projectionSurjectiveAtEta
  refine ⟨(map z, xi), ?_, ?_⟩
  · exact ⟨z, hzC, rfl, hxi⟩
  · exact hzdim

end Omega.Conclusion
