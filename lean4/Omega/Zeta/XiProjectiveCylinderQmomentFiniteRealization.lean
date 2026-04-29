import Omega.POM.ProjectiveOperatorDegeneratesToMomentKernel

namespace Omega.Zeta

/-- Paper label: `thm:xi-projective-cylinder-qmoment-finite-realization`. -/
theorem paper_xi_projective_cylinder_qmoment_finite_realization
    {κ : Type*} [Fintype κ] {q : ℕ}
    (B : κ → Matrix (Fin q) (Fin q) ℝ) (p : Fin q → ℝ) :
    Omega.POM.homogeneousInvariant B p ∧
      Omega.POM.matrixRepresentationIsMomentKernel B ∧
      Omega.POM.spectralRadiusMatches B := by
  exact Omega.POM.paper_pom_projective_operator_degenerates_to_moment_kernel B p

end Omega.Zeta
