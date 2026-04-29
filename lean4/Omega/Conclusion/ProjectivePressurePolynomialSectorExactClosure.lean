import Omega.POM.ProjectiveOperatorDegeneratesToMomentKernel

namespace Omega.Conclusion

open Omega.POM

/-!
This conclusion is the paper-facing wrapper around the already verified POM package: the
projective operator preserves the homogeneous coefficient sector, its monomial-basis matrix is the
moment-kernel matrix, and the packaged spectral-radius seed is therefore identical on both sides.
-/

/-- Paper label: `thm:conclusion-projective-pressure-polynomial-sector-exact-closure`. -/
theorem paper_conclusion_projective_pressure_polynomial_sector_exact_closure
    {κ : Type*} [Fintype κ] {q : ℕ}
    (B : κ → Matrix (Fin q) (Fin q) ℝ) (p : Fin q → ℝ) :
    homogeneousInvariant B p ∧
      matrixRepresentationIsMomentKernel B ∧ spectralRadiusMatches B := by
  exact paper_pom_projective_operator_degenerates_to_moment_kernel B p

end Omega.Conclusion
