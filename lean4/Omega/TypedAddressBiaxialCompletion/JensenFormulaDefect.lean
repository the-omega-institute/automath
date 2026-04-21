import Omega.TypedAddressBiaxialCompletion.JensenDefectFiniteization

namespace Omega.TypedAddressBiaxialCompletion

/-- Appendix-facing Jensen formula wrapper: the finiteized defect is nonnegative and vanishes
exactly on the zero-free radii.
    prop:app-jensen-formula-defect -/
theorem paper_app_jensen_formula_defect (D : JensenDefectFiniteizationData) :
    ∀ {rho : ℝ}, 0 < rho → rho < 1 → 0 ≤ D.defect rho ∧ (D.defect rho = 0 ↔ D.zeroFree rho) := by
  intro rho hrho hrho_lt
  simpa using paper_typed_address_biaxial_completion_jensen_defect_finiteization D hrho hrho_lt

end Omega.TypedAddressBiaxialCompletion
