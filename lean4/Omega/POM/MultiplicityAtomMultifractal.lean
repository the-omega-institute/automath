import Mathlib.Tactic
import Omega.POM.MultiplicityMicrocanonicalEntropy

namespace Omega.POM

noncomputable section

/-- Concrete parameters for the atom multifractal wrapper. The only free constant is
`\log \lambda(1)`; the energy entropy and endpoints are imported from the microcanonical
multiplicity theorem. -/
structure pom_multiplicity_atom_multifractal_data where
  pom_multiplicity_atom_multifractal_log_lambda_one : ℝ

namespace pom_multiplicity_atom_multifractal_data

/-- Affine change from multiplicity energy to atom negative log-probability. -/
def pom_multiplicity_atom_multifractal_alpha
    (D : pom_multiplicity_atom_multifractal_data) (e : ℝ) : ℝ :=
  D.pom_multiplicity_atom_multifractal_log_lambda_one - e

/-- The left endpoint of the atom `alpha` interval, corresponding to energy `log 2`. -/
def pom_multiplicity_atom_multifractal_alpha_left
    (D : pom_multiplicity_atom_multifractal_data) : ℝ :=
  D.pom_multiplicity_atom_multifractal_log_lambda_one - pomMultiplicityEnergyRight

/-- The right endpoint of the atom `alpha` interval, corresponding to energy `log phi`. -/
def pom_multiplicity_atom_multifractal_alpha_right
    (D : pom_multiplicity_atom_multifractal_data) : ℝ :=
  D.pom_multiplicity_atom_multifractal_log_lambda_one - pomMultiplicityEnergyLeft

/-- Atom spectrum obtained from the microcanonical entropy by the affine change
`alpha = log lambda(1) - e`. -/
def pom_multiplicity_atom_multifractal_spectrum
    (D : pom_multiplicity_atom_multifractal_data) (alpha : ℝ) : ℝ :=
  pomMultiplicityEntropy (D.pom_multiplicity_atom_multifractal_log_lambda_one - alpha)

end pom_multiplicity_atom_multifractal_data

open pom_multiplicity_atom_multifractal_data

/-- Concrete atom-spectrum statement: the affine energy-to-atom change transports the
microcanonical entropy, its two endpoint zeros, and the midpoint strict-concavity identity. -/
def pom_multiplicity_atom_multifractal_statement
    (D : pom_multiplicity_atom_multifractal_data) : Prop :=
  (∀ e : ℝ,
      D.pom_multiplicity_atom_multifractal_spectrum
          (D.pom_multiplicity_atom_multifractal_alpha e) =
        pomMultiplicityEntropy e) ∧
    D.pom_multiplicity_atom_multifractal_alpha pomMultiplicityEnergyRight =
      D.pom_multiplicity_atom_multifractal_alpha_left ∧
    D.pom_multiplicity_atom_multifractal_alpha pomMultiplicityEnergyLeft =
      D.pom_multiplicity_atom_multifractal_alpha_right ∧
    D.pom_multiplicity_atom_multifractal_spectrum
        D.pom_multiplicity_atom_multifractal_alpha_left = 0 ∧
    D.pom_multiplicity_atom_multifractal_spectrum
        D.pom_multiplicity_atom_multifractal_alpha_right = 0 ∧
    (∀ alpha₁ alpha₂ : ℝ,
      D.pom_multiplicity_atom_multifractal_spectrum ((alpha₁ + alpha₂) / 2) -
          (D.pom_multiplicity_atom_multifractal_spectrum alpha₁ +
              D.pom_multiplicity_atom_multifractal_spectrum alpha₂) / 2 =
        (alpha₁ - alpha₂) ^ 2 / 4)

/-- Paper label: `prop:pom-multiplicity-atom-multifractal`. The atom spectrum is the existing
microcanonical multiplicity entropy after the affine substitution
`alpha = log lambda(1) - e`; endpoint vanishing and concavity are inherited by algebra. -/
theorem paper_pom_multiplicity_atom_multifractal
    (D : pom_multiplicity_atom_multifractal_data) :
    pom_multiplicity_atom_multifractal_statement D := by
  rcases paper_pom_multiplicity_microcanonical_entropy with
    ⟨_, _, hLeft, hRight, hConcavity⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e
    simp [pom_multiplicity_atom_multifractal_spectrum,
      pom_multiplicity_atom_multifractal_alpha]
  · rfl
  · rfl
  · have harg :
        D.pom_multiplicity_atom_multifractal_log_lambda_one -
            (D.pom_multiplicity_atom_multifractal_log_lambda_one -
              pomMultiplicityEnergyRight) =
          pomMultiplicityEnergyRight := by
      ring
    simp [pom_multiplicity_atom_multifractal_spectrum,
      pom_multiplicity_atom_multifractal_alpha_left, harg, hRight]
  · have harg :
        D.pom_multiplicity_atom_multifractal_log_lambda_one -
            (D.pom_multiplicity_atom_multifractal_log_lambda_one -
              pomMultiplicityEnergyLeft) =
          pomMultiplicityEnergyLeft := by
      ring
    simp [pom_multiplicity_atom_multifractal_spectrum,
      pom_multiplicity_atom_multifractal_alpha_right, harg, hLeft]
  · intro alpha₁ alpha₂
    have h := hConcavity
      (D.pom_multiplicity_atom_multifractal_log_lambda_one - alpha₁)
      (D.pom_multiplicity_atom_multifractal_log_lambda_one - alpha₂)
    unfold pom_multiplicity_atom_multifractal_spectrum
    convert h using 1 <;> ring_nf

end

end Omega.POM
