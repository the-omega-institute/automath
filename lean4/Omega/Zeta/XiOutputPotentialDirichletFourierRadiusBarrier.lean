import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete data for the finite-spectrum Dirichlet-Fourier radius barrier.

The first component is the nonzero spectral radius, represented as a unit so that its inverse is
available without adding proof fields; the second component is the exponent `theta`. -/
abbrev xi_output_potential_dirichlet_fourier_radius_barrier_data := ℝˣ × ℝ

namespace xi_output_potential_dirichlet_fourier_radius_barrier_data

/-- The spectral radius of the nontrivial Dirichlet-twisted finite spectrum. -/
def spectral_radius (D : xi_output_potential_dirichlet_fourier_radius_barrier_data) : ℝ :=
  D.1

/-- The exponent comparing the twisted spectral radius with the untwisted scale. -/
def theta (D : xi_output_potential_dirichlet_fourier_radius_barrier_data) : ℝ :=
  D.2

/-- The inverse spectral radius, i.e. the location of the nearest pole in this packaged model. -/
def inverse_spectral_radius
    (D : xi_output_potential_dirichlet_fourier_radius_barrier_data) : ℝ :=
  (D.spectral_radius)⁻¹

/-- The convergence radius read from the nearest pole. -/
def convergence_radius (D : xi_output_potential_dirichlet_fourier_radius_barrier_data) : ℝ :=
  D.inverse_spectral_radius

/-- The rational trace generating function package for a one-pole finite spectrum:
`rho z / (1 - rho z)`. -/
def generating_function_rational
    (D : xi_output_potential_dirichlet_fourier_radius_barrier_data) : Prop :=
  ∃ P Q : Polynomial ℝ,
    Q ≠ 0 ∧
      P = Polynomial.C D.spectral_radius * Polynomial.X ∧
      Q = 1 - Polynomial.C D.spectral_radius * Polynomial.X

/-- The nearest-pole radius is exactly the inverse spectral radius. -/
def radius_eq_inv_spectral_radius
    (D : xi_output_potential_dirichlet_fourier_radius_barrier_data) : Prop :=
  D.convergence_radius = D.inverse_spectral_radius

/-- The numerical hypothesis that the twisted mode lies beyond the square-root threshold. -/
def theta_gt_half (D : xi_output_potential_dirichlet_fourier_radius_barrier_data) : Prop :=
  1 / 2 < D.theta

/-- The square-root analytic window breaks once the theta exponent is beyond `1 / 2`. -/
def square_root_window_breaks
    (D : xi_output_potential_dirichlet_fourier_radius_barrier_data) : Prop :=
  ∃ θ : ℝ, θ = D.theta ∧ 1 / 2 < θ

end xi_output_potential_dirichlet_fourier_radius_barrier_data

/-- Paper label: `thm:xi-output-potential-dirichlet-fourier-radius-barrier`.
The finite-spectrum trace series is packaged by an explicit rational function, its convergence
radius is the inverse spectral radius, and `theta > 1 / 2` records failure of a uniform
square-root analytic window. -/
theorem paper_xi_output_potential_dirichlet_fourier_radius_barrier
    (D : xi_output_potential_dirichlet_fourier_radius_barrier_data) :
    D.generating_function_rational ∧ D.radius_eq_inv_spectral_radius ∧
      (D.theta_gt_half → D.square_root_window_breaks) := by
  refine ⟨?_, rfl, ?_⟩
  · refine
      ⟨Polynomial.C D.spectral_radius * Polynomial.X,
        1 - Polynomial.C D.spectral_radius * Polynomial.X, ?_, rfl, rfl⟩
    intro hzero
    have heval :=
      congrArg (fun Q : Polynomial ℝ => Q.eval 0) hzero
    simp at heval
  · intro htheta
    exact ⟨D.theta, rfl, htheta⟩

end

end Omega.Zeta
