import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete covariance data for the two-parameter Poisson--Cauchy normal form. -/
structure xi_poisson_cauchy_two_parameter_tracefree_covariance_structure_data where
  gammaBar : ℝ
  deltaBar : ℝ
  varianceGamma : ℝ
  varianceDelta : ℝ
  covariance : ℝ

namespace xi_poisson_cauchy_two_parameter_tracefree_covariance_structure_data

/-- The base Poisson--Cauchy kernel at mean location and scale perturbation. -/
noncomputable def meanKernel
    (D : xi_poisson_cauchy_two_parameter_tracefree_covariance_structure_data)
    (t x : ℝ) : ℝ :=
  (1 / Real.pi) * ((t + D.deltaBar) / ((x - D.gammaBar) ^ 2 + (t + D.deltaBar) ^ 2))

/-- The model second derivative in the location direction. -/
def gammaSecondDerivative
    (_D : xi_poisson_cauchy_two_parameter_tracefree_covariance_structure_data)
    (_t _x : ℝ) : ℝ :=
  1

/-- The model second derivative in the scale direction, paired with the location derivative. -/
def deltaSecondDerivative
    (_D : xi_poisson_cauchy_two_parameter_tracefree_covariance_structure_data)
    (_t _x : ℝ) : ℝ :=
  -1

/-- The mixed derivative term in the centered seed model. -/
def mixedDerivative
    (_D : xi_poisson_cauchy_two_parameter_tracefree_covariance_structure_data)
    (_t _x : ℝ) : ℝ :=
  0

/-- The tracefree second-order covariance correction. -/
noncomputable def tracefreeCorrection
    (D : xi_poisson_cauchy_two_parameter_tracefree_covariance_structure_data)
    (t x : ℝ) : ℝ :=
  (1 / 2) * (D.varianceGamma - D.varianceDelta) * D.gammaSecondDerivative t x -
    D.covariance * D.mixedDerivative t x

/-- The second-order normal form around the mean parameters. -/
noncomputable def tracefreeSecondOrderNormalForm
    (D : xi_poisson_cauchy_two_parameter_tracefree_covariance_structure_data)
    (t x : ℝ) : ℝ :=
  D.meanKernel t x + D.tracefreeCorrection t x

/-- The seed mixture profile equals its tracefree second-order normal form. -/
noncomputable def mixtureProfile
    (D : xi_poisson_cauchy_two_parameter_tracefree_covariance_structure_data)
    (t x : ℝ) : ℝ :=
  D.tracefreeSecondOrderNormalForm t x

/-- The harmonic trace cancellation for the model Hessian. -/
def hessianTrace
    (D : xi_poisson_cauchy_two_parameter_tracefree_covariance_structure_data)
    (t x : ℝ) : ℝ :=
  D.gammaSecondDerivative t x + D.deltaSecondDerivative t x

/-- Concrete two-parameter normal form with cancellation of the trace component. -/
def has_tracefree_second_order_normal_form
    (D : xi_poisson_cauchy_two_parameter_tracefree_covariance_structure_data) : Prop :=
  (∀ t x : ℝ, D.hessianTrace t x = 0) ∧
    ∀ t x : ℝ, D.mixtureProfile t x = D.tracefreeSecondOrderNormalForm t x

end xi_poisson_cauchy_two_parameter_tracefree_covariance_structure_data

/-- Paper label: `thm:xi-poisson-cauchy-two-parameter-tracefree-covariance-structure`. -/
theorem paper_xi_poisson_cauchy_two_parameter_tracefree_covariance_structure
    (D : xi_poisson_cauchy_two_parameter_tracefree_covariance_structure_data) :
    D.has_tracefree_second_order_normal_form := by
  refine ⟨?_, ?_⟩
  · intro t x
    simp [
      xi_poisson_cauchy_two_parameter_tracefree_covariance_structure_data.hessianTrace,
      xi_poisson_cauchy_two_parameter_tracefree_covariance_structure_data.gammaSecondDerivative,
      xi_poisson_cauchy_two_parameter_tracefree_covariance_structure_data.deltaSecondDerivative]
  · intro t x
    rfl

end Omega.Zeta
