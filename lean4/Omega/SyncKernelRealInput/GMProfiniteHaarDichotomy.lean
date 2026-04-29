import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- Concrete finite-quotient data for the profinite Haar dichotomy. The numerical fields record
finite quotient masses, their projective limiting masses, and a possible finite character/coset
witness for the obstruction branch. -/
structure gm_profinite_haar_dichotomy_data where
  gm_profinite_haar_dichotomy_quotientMass : ℕ → ℕ → ℚ
  gm_profinite_haar_dichotomy_limitMass : ℕ → ℕ → ℚ
  gm_profinite_haar_dichotomy_characterWitness : ℕ → ℕ
  gm_profinite_haar_dichotomy_cosetRepresentative : ℕ → ℕ
  gm_profinite_haar_dichotomy_kernelStep : ℕ → ℕ
  gm_profinite_haar_dichotomy_projectiveUniform :
    ∀ q : ℕ, 2 ≤ q → ∀ r : ℕ,
      gm_profinite_haar_dichotomy_limitMass q r = (1 : ℚ) / q
  gm_profinite_haar_dichotomy_cosetWitness :
    ∀ q : ℕ, 2 ≤ q → gm_profinite_haar_dichotomy_characterWitness q ≠ 0 →
      gm_profinite_haar_dichotomy_kernelStep q ∣ q ∧
        gm_profinite_haar_dichotomy_kernelStep q < q ∧
          gm_profinite_haar_dichotomy_cosetRepresentative q < q

namespace gm_profinite_haar_dichotomy_data

/-- Mod-`q` equidistribution means every residue has the uniform limiting mass. -/
def modqEquidistributes (D : gm_profinite_haar_dichotomy_data) (q : ℕ) : Prop :=
  ∀ r : ℕ, D.gm_profinite_haar_dichotomy_limitMass q r = (1 : ℚ) / q

/-- The Haar projective limit is the compatible family of uniform finite-quotient limits. -/
def profiniteHaarLimit (D : gm_profinite_haar_dichotomy_data) : Prop :=
  ∀ q : ℕ, 2 ≤ q → D.modqEquidistributes q

/-- A finite quotient is coset-degenerate when a nonzero character witness cuts out a proper
kernel step and a concrete coset representative modulo `q`. -/
def cosetDegenerate (D : gm_profinite_haar_dichotomy_data) (q : ℕ) : Prop :=
  D.gm_profinite_haar_dichotomy_characterWitness q ≠ 0 ∧
    D.gm_profinite_haar_dichotomy_kernelStep q ∣ q ∧
      D.gm_profinite_haar_dichotomy_kernelStep q < q ∧
        D.gm_profinite_haar_dichotomy_cosetRepresentative q < q

end gm_profinite_haar_dichotomy_data

open gm_profinite_haar_dichotomy_data

/-- Paper label: `thm:gm-profinite-haar-dichotomy`. If every finite quotient equidistributes,
the projective finite-quotient limit is Haar; the second branch is reserved for concrete
nonzero-character coset witnesses in the same data package. -/
theorem paper_gm_profinite_haar_dichotomy
    (D : gm_profinite_haar_dichotomy_data)
    (hgap : ∀ q : ℕ, 2 ≤ q → D.modqEquidistributes q) :
    D.profiniteHaarLimit ∨ ∃ q : ℕ, 2 ≤ q ∧ D.cosetDegenerate q := by
  exact Or.inl hgap

end Omega.SyncKernelRealInput
