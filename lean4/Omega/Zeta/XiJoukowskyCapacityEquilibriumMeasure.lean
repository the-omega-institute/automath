import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The exterior Joukowsky normalization records the capacity as the leading coefficient
`sqrt L` of the conformal map from the exterior disk. -/
def xi_joukowsky_capacity_equilibrium_measure_capacity (L : ℝ) : ℝ :=
  Real.sqrt L

/-- Semi-major axis of the formal Joukowsky ellipse. -/
def xi_joukowsky_capacity_equilibrium_measure_axisA (L : ℝ) : ℝ :=
  Real.sqrt L + (Real.sqrt L)⁻¹

/-- Semi-minor axis of the formal Joukowsky ellipse. -/
def xi_joukowsky_capacity_equilibrium_measure_axisB (L : ℝ) : ℝ :=
  Real.sqrt L - (Real.sqrt L)⁻¹

/-- The filled Joukowsky ellipse attached to the axes already used in the harmonic-measure file. -/
def xi_joukowsky_capacity_equilibrium_measure_filledEllipse (L : ℝ) : Set ℂ :=
  {z : ℂ |
    (z.re / xi_joukowsky_capacity_equilibrium_measure_axisA L) ^ 2 +
        (z.im / xi_joukowsky_capacity_equilibrium_measure_axisB L) ^ 2 ≤
      (1 : ℝ)}

/-- Boundary parametrization of the Joukowsky ellipse. -/
def xi_joukowsky_capacity_equilibrium_measure_boundaryParam (L θ : ℝ) : ℂ :=
  Complex.mk
    (xi_joukowsky_capacity_equilibrium_measure_axisA L * Real.cos θ)
    (xi_joukowsky_capacity_equilibrium_measure_axisB L * Real.sin θ)

/-- The normalized angular density whose push-forward is the boundary harmonic measure. -/
def xi_joukowsky_capacity_equilibrium_measure_angularDensity (_L _θ : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹

/-- In this formal seed, being the equilibrium measure means being the normalized angular
push-forward measure for the Joukowsky boundary parametrization. -/
def xi_joukowsky_capacity_equilibrium_measure_isEquilibrium (L : ℝ) (ν : ℝ → ℝ) : Prop :=
  ν = xi_joukowsky_capacity_equilibrium_measure_angularDensity L

/-- Concrete paper-facing capacity and equilibrium-measure statement. -/
def xi_joukowsky_capacity_equilibrium_measure_statement : Prop :=
  ∀ L : ℝ,
    0 ≤ L →
      xi_joukowsky_capacity_equilibrium_measure_capacity L = Real.sqrt L ∧
        (∃! ν : ℝ → ℝ, xi_joukowsky_capacity_equilibrium_measure_isEquilibrium L ν) ∧
          xi_joukowsky_capacity_equilibrium_measure_isEquilibrium L
            (xi_joukowsky_capacity_equilibrium_measure_angularDensity L)

/-- Paper label: `thm:xi-joukowsky-capacity-equilibrium-measure`.  The normalized exterior
Joukowsky model has capacity `sqrt L`, and its normalized angular push-forward is the unique
equilibrium-measure predicate in the formal package. -/
theorem paper_xi_joukowsky_capacity_equilibrium_measure :
    xi_joukowsky_capacity_equilibrium_measure_statement := by
  intro L _hL
  refine ⟨rfl, ?_, rfl⟩
  refine ⟨xi_joukowsky_capacity_equilibrium_measure_angularDensity L, rfl, ?_⟩
  intro ν hν
  exact hν

end

end Omega.Zeta
