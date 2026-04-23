import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Omega.POM.DerivedSchurDirichletRamanujanParseval

namespace Omega.DerivedConsequences

open scoped BigOperators ComplexConjugate

/-- Paper label: `cor:derived-schur-dirichlet-nonprincipal-energy-variance`.  If the recorded
Schur/Dirichlet amplitude is already centered, then the principal channel vanishes, so the full
Parseval--Gram energy is carried entirely by the nonprincipal characters. -/
theorem paper_derived_schur_dirichlet_nonprincipal_energy_variance
    (D : Omega.POM.DerivedSchurDirichletRamanujanParsevalData)
    (hcentered : ∑ a : Fin D.q, D.leftChannel a = 0)
    (hselfChannel : D.rightChannel = D.leftChannel)
    (hselfFunctional : D.rightFunctional = D.leftFunctional) :
    D.leftFunctional D.principal = 0 ∧
      Finset.sum (Finset.univ.erase D.principal)
          (fun χ : Fin D.q => D.leftFunctional χ * conj (D.leftFunctional χ)) =
        (D.q : ℂ) * (∑ a : Fin D.q, D.leftChannel a * conj (D.leftChannel a)) := by
  rcases Omega.POM.paper_derived_schur_dirichlet_ramanujan_parseval D with
    ⟨hprincipalTrace, hparseval⟩
  have hprincipalTrace' := hprincipalTrace
  rw [Omega.POM.DerivedSchurDirichletRamanujanParsevalData.principalRamanujanTrace] at hprincipalTrace'
  have hprincipal : D.leftFunctional D.principal = 0 := by
    simpa [hcentered] using hprincipalTrace'
  have henergy := hparseval
  rw [Omega.POM.DerivedSchurDirichletRamanujanParsevalData.parsevalGramIdentity,
    hselfChannel, hselfFunctional] at henergy
  refine ⟨hprincipal, ?_⟩
  let paper_derived_schur_dirichlet_nonprincipal_energy_variance_energyTerm : Fin D.q → ℂ :=
    fun χ => D.leftFunctional χ * conj (D.leftFunctional χ)
  calc
    Finset.sum (Finset.univ.erase D.principal)
        paper_derived_schur_dirichlet_nonprincipal_energy_variance_energyTerm =
        Finset.sum (Finset.univ.erase D.principal)
            paper_derived_schur_dirichlet_nonprincipal_energy_variance_energyTerm +
          paper_derived_schur_dirichlet_nonprincipal_energy_variance_energyTerm D.principal := by
            simp [paper_derived_schur_dirichlet_nonprincipal_energy_variance_energyTerm,
              hprincipal]
    _ = ∑ χ : Fin D.q, paper_derived_schur_dirichlet_nonprincipal_energy_variance_energyTerm χ := by
          exact Finset.sum_erase_add (s := Finset.univ) (a := D.principal)
            (f := paper_derived_schur_dirichlet_nonprincipal_energy_variance_energyTerm) (by simp)
    _ = (D.q : ℂ) * (∑ a : Fin D.q, D.leftChannel a * conj (D.leftChannel a)) := by
          simpa [paper_derived_schur_dirichlet_nonprincipal_energy_variance_energyTerm] using
            henergy

end Omega.DerivedConsequences
