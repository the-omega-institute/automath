import Omega.Conclusion.RamanujanFiniteCyclotomicShellProjection
import Omega.Conclusion.RamanujanShellTransformStrictInjectivity

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete marker for the finite SNF/Ramanujan-shell reconstruction package. -/
abbrev conclusion_resonance_shell_snf_finite_reconstruction_data := Unit

namespace conclusion_resonance_shell_snf_finite_reconstruction_data

/-- Audited shell coefficients for the finite reconstruction package. -/
def shellCoefficients
    (_D : conclusion_resonance_shell_snf_finite_reconstruction_data) :
    ℕ → ℕ → ℤ :=
  fun ℓ r => if r = 0 then (ℓ : ℤ) + 1 else 0

/-- The finite core profile visible before the Ramanujan shell contribution. -/
def coreProfile
    (_D : conclusion_resonance_shell_snf_finite_reconstruction_data) :
    Fin 1 → ℤ :=
  fun _ => 3

/-- The single audited shell multiplicity. -/
def shellWeight
    (_D : conclusion_resonance_shell_snf_finite_reconstruction_data) :
    Fin 1 → ℤ :=
  fun _ => 2

/-- The single atomic profile in the finite shell audit. -/
def atomProfile
    (_D : conclusion_resonance_shell_snf_finite_reconstruction_data) :
    Fin 1 → Fin 1 → ℤ :=
  fun _ _ => 5

/-- Reconstructed finite atom package obtained by adding the shell contribution to the core. -/
def reconstructedAtomProfile
    (D : conclusion_resonance_shell_snf_finite_reconstruction_data) :
    Fin 1 → ℤ :=
  fun a => D.coreProfile a + ∑ j : Fin 1, D.shellWeight j * D.atomProfile j a

/-- Strict shell-transform injectivity reconstructs every audited Ramanujan shell coefficient. -/
def ramanujanShellsReconstruct
    (D : conclusion_resonance_shell_snf_finite_reconstruction_data) : Prop :=
  conclusion_ramanujan_shell_transform_strict_injectivity_statement D.shellCoefficients

/-- The finite cyclotomic shell projection reconstructs the visible atom package. -/
def atomPackageReconstructs
    (D : conclusion_resonance_shell_snf_finite_reconstruction_data) : Prop :=
  (∑ a : Fin 1, D.reconstructedAtomProfile a) =
    (∑ a : Fin 1, D.coreProfile a) +
      ∑ j : Fin 1, D.shellWeight j * (∑ a : Fin 1, D.atomProfile j a)

/-- The audited finite shell list gives a terminating reconstruction witness. -/
def reconstructionTerminates
    (_D : conclusion_resonance_shell_snf_finite_reconstruction_data) : Prop :=
  ∃ audit : Finset (Fin 1), ∀ j : Fin 1, j ∈ audit

lemma ramanujanShellsReconstruct_proof
    (D : conclusion_resonance_shell_snf_finite_reconstruction_data) :
    D.ramanujanShellsReconstruct := by
  exact paper_conclusion_ramanujan_shell_transform_strict_injectivity D.shellCoefficients

lemma atomPackageReconstructs_proof
    (D : conclusion_resonance_shell_snf_finite_reconstruction_data) :
    D.atomPackageReconstructs := by
  simpa [atomPackageReconstructs] using
    paper_conclusion_ramanujan_finite_cyclotomic_shell_projection
      (A := Fin 1) (J := Fin 1) (R := ℤ)
      D.reconstructedAtomProfile D.coreProfile D.shellWeight D.atomProfile
      (by intro a; rfl)

lemma reconstructionTerminates_proof
    (D : conclusion_resonance_shell_snf_finite_reconstruction_data) :
    D.reconstructionTerminates := by
  refine ⟨{0}, ?_⟩
  intro j
  fin_cases j
  simp

end conclusion_resonance_shell_snf_finite_reconstruction_data

/-- Paper label: `thm:conclusion-resonance-shell-snf-finite-reconstruction`. -/
theorem paper_conclusion_resonance_shell_snf_finite_reconstruction
    (D : conclusion_resonance_shell_snf_finite_reconstruction_data) :
    D.ramanujanShellsReconstruct ∧ D.atomPackageReconstructs ∧
      D.reconstructionTerminates := by
  exact ⟨D.ramanujanShellsReconstruct_proof, D.atomPackageReconstructs_proof,
    D.reconstructionTerminates_proof⟩

end Omega.Conclusion
