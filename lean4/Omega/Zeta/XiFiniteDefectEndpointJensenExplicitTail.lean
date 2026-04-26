import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Omega.Zeta.XiJensenBoundaryPotentialFiniteDefectExplicit

namespace Omega.Zeta

open Filter MeasureTheory
open scoped BigOperators

noncomputable section

/-- Paper-facing explicit-tail statement for the finite-defect endpoint Jensen profile. -/
def xi_finite_defect_endpoint_jensen_explicit_tail_statement
    {ι : Type} [Fintype ι] [DecidableEq ι] (γ δ : ι → ℝ) (m : ι → ℕ) : Prop :=
  (∀ x : ℝ,
      xi_jensen_boundary_potential_finite_defect_explicit_profile γ δ m x =
        ∑ i, xi_jensen_boundary_potential_finite_defect_explicit_singleProfile γ δ m i x) ∧
    Integrable (xi_jensen_boundary_potential_finite_defect_explicit_profile γ δ m) ∧
    (∫ x, xi_jensen_boundary_potential_finite_defect_explicit_profile γ δ m x =
      4 * Real.pi * ∑ i, (m i : ℝ) * (δ i / (1 + δ i))) ∧
    Filter.Tendsto (xi_jensen_boundary_potential_finite_defect_explicit_profile γ δ m)
      Filter.atTop (nhds 0)

/-- Paper label: `thm:xi-finite-defect-endpoint-jensen-explicit-tail`. -/
theorem paper_xi_finite_defect_endpoint_jensen_explicit_tail
    {ι : Type} [Fintype ι] [DecidableEq ι] (γ δ : ι → ℝ) (m : ι → ℕ)
    (hδ0 : ∀ i, 0 < δ i) (_hδ1 : ∀ i, δ i < 1) :
    xi_finite_defect_endpoint_jensen_explicit_tail_statement γ δ m := by
  exact paper_xi_jensen_boundary_potential_finite_defect_explicit γ δ m hδ0

end

end Omega.Zeta
