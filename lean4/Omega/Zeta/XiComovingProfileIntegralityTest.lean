import Omega.Zeta.XiComovingProfileCompleteReconstruction

namespace Omega.Zeta

/-- Boundary pole/residue data equipped with the proposed natural multiplicities. -/
structure xi_comoving_profile_integrality_test_data where
  defectCount : ℕ
  poleGamma : Fin defectCount → ℝ
  poleDelta : Fin defectCount → ℝ
  poleResidue : Fin defectCount → ℝ
  recoveredMultiplicity : Fin defectCount → ℕ

namespace xi_comoving_profile_integrality_test_data

/-- The closed-form divisibility criterion for the recovered residues. -/
def residueMultiplicityCriterion (D : xi_comoving_profile_integrality_test_data) : Prop :=
  ∀ j, D.poleResidue j = 4 * (D.recoveredMultiplicity j : ℝ) * D.poleDelta j

/-- A concrete integer-multiplicity defect certificate for the integrality test. -/
structure xi_comoving_profile_integrality_test_certificate
    (D : xi_comoving_profile_integrality_test_data) where
  residue_formula : D.residueMultiplicityCriterion

/-- Integer-multiplicity defects exist exactly when the recovered residues pass the formula. -/
def admitsIntegerMultiplicityDefects (D : xi_comoving_profile_integrality_test_data) : Prop :=
  Nonempty (xi_comoving_profile_integrality_test_certificate D)

/-- Convert a successful residue test into the complete reconstruction package. -/
def xi_comoving_profile_integrality_test_reconstructionData
    (D : xi_comoving_profile_integrality_test_data) (h : D.residueMultiplicityCriterion) :
    xi_comoving_profile_complete_reconstruction_data where
  defectCount := D.defectCount
  poleGamma := D.poleGamma
  poleDelta := D.poleDelta
  poleResidue := D.poleResidue
  multiplicity := D.recoveredMultiplicity
  residue_formula := h

end xi_comoving_profile_integrality_test_data

open xi_comoving_profile_integrality_test_data

/-- Paper label: `cor:xi-comoving-profile-integrality-test`. -/
theorem paper_xi_comoving_profile_integrality_test
    (D : xi_comoving_profile_integrality_test_data) :
    D.admitsIntegerMultiplicityDefects ↔ D.residueMultiplicityCriterion := by
  constructor
  · intro h
    rcases h with ⟨C⟩
    exact C.residue_formula
  · intro h
    exact ⟨{ residue_formula := h }⟩

end Omega.Zeta
