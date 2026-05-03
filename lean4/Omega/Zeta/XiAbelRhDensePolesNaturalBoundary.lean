import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete Abel-Weil boundary data.  The pole set is the modeled image of the critical-line
zeros on the unit circle; non-removable singularities record the no-cancellation output. -/
structure xi_abel_rh_dense_poles_natural_boundary_data where
  xi_abel_rh_dense_poles_natural_boundary_poleSet : Set ℂ
  xi_abel_rh_dense_poles_natural_boundary_nonremovableSingularities : Set ℂ
  xi_abel_rh_dense_poles_natural_boundary_analyticContinuationAcross : ℂ → Prop

/-- The unit circle in the Abel variable. -/
def xi_abel_rh_dense_poles_natural_boundary_unitCircle : Set ℂ :=
  {z : ℂ | ‖z‖ = 1}

/-- Density of the Abel-Weil pole set on the unit circle. -/
def xi_abel_rh_dense_poles_natural_boundary_densePoles
    (D : xi_abel_rh_dense_poles_natural_boundary_data) : Prop :=
  ∀ ζ ∈ xi_abel_rh_dense_poles_natural_boundary_unitCircle, ∀ ε : ℝ, 0 < ε →
    ∃ r ∈ D.xi_abel_rh_dense_poles_natural_boundary_poleSet,
      r ∈ xi_abel_rh_dense_poles_natural_boundary_unitCircle ∧ dist r ζ < ε

/-- The no-cancellation hypothesis: every modeled boundary pole is non-removable. -/
def xi_abel_rh_dense_poles_natural_boundary_noCancellation
    (D : xi_abel_rh_dense_poles_natural_boundary_data) : Prop :=
  ∀ r ∈ D.xi_abel_rh_dense_poles_natural_boundary_poleSet,
    r ∈ D.xi_abel_rh_dense_poles_natural_boundary_nonremovableSingularities

/-- Any analytic continuation across a boundary point removes singularities on some boundary
arc around that point. -/
def xi_abel_rh_dense_poles_natural_boundary_continuationClearsArc
    (D : xi_abel_rh_dense_poles_natural_boundary_data) : Prop :=
  ∀ ζ ∈ xi_abel_rh_dense_poles_natural_boundary_unitCircle,
    D.xi_abel_rh_dense_poles_natural_boundary_analyticContinuationAcross ζ →
      ∃ ε : ℝ, 0 < ε ∧
        ∀ r ∈ xi_abel_rh_dense_poles_natural_boundary_unitCircle, dist r ζ < ε →
          r ∉ D.xi_abel_rh_dense_poles_natural_boundary_nonremovableSingularities

/-- The unit circle is a natural boundary: no boundary point admits analytic continuation
across it. -/
def xi_abel_rh_dense_poles_natural_boundary_naturalBoundary
    (D : xi_abel_rh_dense_poles_natural_boundary_data) : Prop :=
  ∀ ζ ∈ xi_abel_rh_dense_poles_natural_boundary_unitCircle,
    ¬ D.xi_abel_rh_dense_poles_natural_boundary_analyticContinuationAcross ζ

/-- Concrete theorem statement for `thm:xi-abel-rh-dense-poles-natural-boundary`. -/
def xi_abel_rh_dense_poles_natural_boundary_statement
    (D : xi_abel_rh_dense_poles_natural_boundary_data) : Prop :=
  xi_abel_rh_dense_poles_natural_boundary_densePoles D →
    xi_abel_rh_dense_poles_natural_boundary_noCancellation D →
      xi_abel_rh_dense_poles_natural_boundary_continuationClearsArc D →
        xi_abel_rh_dense_poles_natural_boundary_naturalBoundary D

/-- Paper label: `thm:xi-abel-rh-dense-poles-natural-boundary`. -/
theorem paper_xi_abel_rh_dense_poles_natural_boundary
    (D : xi_abel_rh_dense_poles_natural_boundary_data) :
    xi_abel_rh_dense_poles_natural_boundary_statement D := by
  intro hdense hnocancel hclear ζ hζ hcont
  rcases hclear ζ hζ hcont with ⟨ε, hε, hregular⟩
  rcases hdense ζ hζ ε hε with ⟨r, hr_pole, hr_circle, hr_dist⟩
  exact hregular r hr_circle hr_dist (hnocancel r hr_pole)

end Omega.Zeta
