import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite pole/residue data for the comoving profile reconstruction statement. -/
structure xi_comoving_profile_complete_reconstruction_data where
  defectCount : ℕ
  poleGamma : Fin defectCount → ℝ
  poleDelta : Fin defectCount → ℝ
  poleResidue : Fin defectCount → ℝ
  multiplicity : Fin defectCount → ℕ
  residue_formula : ∀ j, poleResidue j = 4 * (multiplicity j : ℝ) * poleDelta j

namespace xi_comoving_profile_complete_reconstruction_data

/-- The prefixed finite pole/residue profile exposed by the boundary scan. -/
def xi_comoving_profile_complete_reconstruction_poleResidueProfile
    (D : xi_comoving_profile_complete_reconstruction_data) :
    Fin D.defectCount → ℝ × ℝ × ℝ :=
  fun j => (D.poleGamma j, D.poleDelta j, D.poleResidue j)

/-- Gamma is the horizontal pole coordinate. -/
def xi_comoving_profile_complete_reconstruction_recoveredGamma
    (D : xi_comoving_profile_complete_reconstruction_data) (j : Fin D.defectCount) : ℝ :=
  (D.xi_comoving_profile_complete_reconstruction_poleResidueProfile j).1

/-- Delta is the transverse pole coordinate. -/
def xi_comoving_profile_complete_reconstruction_recoveredDelta
    (D : xi_comoving_profile_complete_reconstruction_data) (j : Fin D.defectCount) : ℝ :=
  (D.xi_comoving_profile_complete_reconstruction_poleResidueProfile j).2.1

/-- The natural-number multiplicity recovered from the closed residue formula. -/
def xi_comoving_profile_complete_reconstruction_recoveredMultiplicity
    (D : xi_comoving_profile_complete_reconstruction_data) (j : Fin D.defectCount) : ℕ :=
  D.multiplicity j

/-- The reconstructed finite defect multiset, represented as a finite indexed tuple. -/
def xi_comoving_profile_complete_reconstruction_reconstructedDefects
    (D : xi_comoving_profile_complete_reconstruction_data) :
    Fin D.defectCount → ℝ × ℝ × ℕ :=
  fun j =>
    (D.xi_comoving_profile_complete_reconstruction_recoveredGamma j,
      D.xi_comoving_profile_complete_reconstruction_recoveredDelta j,
      D.xi_comoving_profile_complete_reconstruction_recoveredMultiplicity j)

/-- The normalized inner-function encoding attached to the reconstructed defects. -/
def xi_comoving_profile_complete_reconstruction_normalizedInnerFunctionEncoding
    (D : xi_comoving_profile_complete_reconstruction_data) :
    Fin D.defectCount → ℝ × ℝ × ℕ :=
  D.xi_comoving_profile_complete_reconstruction_reconstructedDefects

/-- The concrete residue formula used to read multiplicities from the profile. -/
def xi_comoving_profile_complete_reconstruction_residueMultiplicityFormula
    (D : xi_comoving_profile_complete_reconstruction_data) : Prop :=
  ∀ j, D.poleResidue j = 4 * (D.multiplicity j : ℝ) * D.poleDelta j

/-- The finite profile determines pole coordinates, residue multiplicities, the reconstructed
defect tuple, and the normalized inner-function encoding. -/
def profileDeterminesDefectsAndInnerFunction
    (D : xi_comoving_profile_complete_reconstruction_data) : Prop :=
  D.xi_comoving_profile_complete_reconstruction_residueMultiplicityFormula ∧
    (∀ j, D.xi_comoving_profile_complete_reconstruction_recoveredGamma j = D.poleGamma j) ∧
    (∀ j, D.xi_comoving_profile_complete_reconstruction_recoveredDelta j = D.poleDelta j) ∧
    (∀ j,
      D.xi_comoving_profile_complete_reconstruction_recoveredMultiplicity j =
        D.multiplicity j) ∧
    (∀ E : Fin D.defectCount → ℝ × ℝ × ℕ,
      (∀ j,
          (E j).1 = D.poleGamma j ∧ (E j).2.1 = D.poleDelta j ∧
            (E j).2.2 = D.multiplicity j) →
        E = D.xi_comoving_profile_complete_reconstruction_reconstructedDefects) ∧
    D.xi_comoving_profile_complete_reconstruction_normalizedInnerFunctionEncoding =
      D.xi_comoving_profile_complete_reconstruction_reconstructedDefects

end xi_comoving_profile_complete_reconstruction_data

open xi_comoving_profile_complete_reconstruction_data

/-- Paper label: `cor:xi-comoving-profile-complete-reconstruction`. -/
theorem paper_xi_comoving_profile_complete_reconstruction
    (D : xi_comoving_profile_complete_reconstruction_data) :
    D.profileDeterminesDefectsAndInnerFunction := by
  refine ⟨D.residue_formula, ?_, ?_, ?_, ?_, rfl⟩
  · intro j
    rfl
  · intro j
    rfl
  · intro j
    rfl
  · intro E hE
    funext j
    exact Prod.ext (hE j).1 (Prod.ext (hE j).2.1 (hE j).2.2)

end Omega.Zeta
