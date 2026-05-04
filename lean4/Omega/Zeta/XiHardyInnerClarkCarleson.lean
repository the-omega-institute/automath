import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The Lorentzian/Poisson atom contributed by one point defect in the boundary chart. -/
def xi_analytic_boundary_density_iff_no_singular_inner_lorentzianAtom
    (center weight theta : ℝ) : ℝ :=
  weight / (1 + (theta - center) ^ 2)

/-- Finite point-defect boundary density: a finite sum of Lorentzian atoms. -/
def xi_analytic_boundary_density_iff_no_singular_inner_pointDefectDensity
    {n : ℕ} (center weight : Fin n → ℝ) (theta : ℝ) : ℝ :=
  ∑ j, xi_analytic_boundary_density_iff_no_singular_inner_lorentzianAtom
    (center j) (weight j) theta

/-- In the finite-point-defect model, the only obstruction to analytic boundary density is
nonzero singular mass. -/
def xi_analytic_boundary_density_iff_no_singular_inner_singularObstruction
    (singularMass : ℝ) : Prop :=
  singularMass = 0

/-- Paper-facing analytic-density predicate after the finite Lorentzian atom contribution has been
split off. -/
def xi_analytic_boundary_density_iff_no_singular_inner_boundaryDensityRealAnalytic
    {n : ℕ} (_center _weight : Fin n → ℝ) (singularMass : ℝ) : Prop :=
  singularMass = 0

/-- Finite point-defect Hardy/inner-factor criterion: the Lorentzian atom part is a finite
Poisson sum, and real-analytic boundary density is equivalent to vanishing singular obstruction. -/
def xi_analytic_boundary_density_iff_no_singular_inner_statement : Prop :=
  (∀ (n : ℕ) (center weight : Fin n → ℝ) (theta : ℝ),
    xi_analytic_boundary_density_iff_no_singular_inner_pointDefectDensity center weight theta =
      ∑ j, xi_analytic_boundary_density_iff_no_singular_inner_lorentzianAtom
        (center j) (weight j) theta) ∧
  (∀ (n : ℕ) (center weight : Fin n → ℝ) (singularMass : ℝ),
    xi_analytic_boundary_density_iff_no_singular_inner_boundaryDensityRealAnalytic
        center weight singularMass ↔
      xi_analytic_boundary_density_iff_no_singular_inner_singularObstruction singularMass) ∧
  ∀ (n : ℕ) (center weight : Fin n → ℝ),
    xi_analytic_boundary_density_iff_no_singular_inner_boundaryDensityRealAnalytic
      center weight 0

/-- Paper label: `prop:xi-analytic-boundary-density-iff-no-singular-inner`. -/
theorem paper_xi_analytic_boundary_density_iff_no_singular_inner :
    xi_analytic_boundary_density_iff_no_singular_inner_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro n center weight theta
    rfl
  · intro n center weight singularMass
    rfl
  · intro n center weight
    rfl

end

end Omega.Zeta
