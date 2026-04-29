import Omega.Zeta.XiJensenBoundaryPotentialFiniteDefectExplicit

namespace Omega.Conclusion

open Filter MeasureTheory
open scoped BigOperators

noncomputable section

/-- Concrete finite-zero data for the Jensen-defect Poisson-slice formula. -/
structure conclusion_jensen_defect_poisson_slice_finite_data where
  zeroCount : ℕ
  center : Fin zeroCount → ℝ
  defectDepth : Fin zeroCount → ℝ
  multiplicity : Fin zeroCount → ℕ
  defectDepth_pos : ∀ i, 0 < defectDepth i

/-- The single Poisson-slice contribution of one finite zero. -/
noncomputable def conclusion_jensen_defect_poisson_slice_finite_poissonSlice
    (D : conclusion_jensen_defect_poisson_slice_finite_data) (i : Fin D.zeroCount)
    (x : ℝ) : ℝ :=
  Omega.Zeta.xi_jensen_boundary_potential_finite_defect_explicit_singleProfile D.center
    D.defectDepth D.multiplicity i x

/-- The finite Jensen defect profile obtained by summing all Poisson slices. -/
noncomputable def conclusion_jensen_defect_poisson_slice_finite_jensenFiniteProfile
    (D : conclusion_jensen_defect_poisson_slice_finite_data) (x : ℝ) : ℝ :=
  Omega.Zeta.xi_jensen_boundary_potential_finite_defect_explicit_profile D.center
    D.defectDepth D.multiplicity x

/-- Concrete finite-zero Poisson-slice statement. -/
def conclusion_jensen_defect_poisson_slice_finite_statement
    (D : conclusion_jensen_defect_poisson_slice_finite_data) : Prop :=
  (∀ x : ℝ,
      conclusion_jensen_defect_poisson_slice_finite_jensenFiniteProfile D x =
        ∑ i : Fin D.zeroCount,
          conclusion_jensen_defect_poisson_slice_finite_poissonSlice D i x) ∧
    Integrable (conclusion_jensen_defect_poisson_slice_finite_jensenFiniteProfile D) ∧
      (∫ x, conclusion_jensen_defect_poisson_slice_finite_jensenFiniteProfile D x =
        4 * Real.pi *
          ∑ i : Fin D.zeroCount,
            (D.multiplicity i : ℝ) * (D.defectDepth i / (1 + D.defectDepth i))) ∧
        Filter.Tendsto (conclusion_jensen_defect_poisson_slice_finite_jensenFiniteProfile D)
          Filter.atTop (nhds 0)

/-- Paper label: `cor:conclusion-jensen-defect-poisson-slice-finite`. -/
theorem paper_conclusion_jensen_defect_poisson_slice_finite
    (D : conclusion_jensen_defect_poisson_slice_finite_data) :
    conclusion_jensen_defect_poisson_slice_finite_statement D := by
  simpa [conclusion_jensen_defect_poisson_slice_finite_statement,
    conclusion_jensen_defect_poisson_slice_finite_jensenFiniteProfile,
    conclusion_jensen_defect_poisson_slice_finite_poissonSlice] using
      Omega.Zeta.paper_xi_jensen_boundary_potential_finite_defect_explicit D.center
        D.defectDepth D.multiplicity D.defectDepth_pos

end

end Omega.Conclusion
