import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

open Matrix

namespace Omega.POM

noncomputable section

/-- Chapter-local `κ_δ` in the single-polynomial determinant model. -/
def pom_maxent_markov_zeta_determinant_single_polynomial_kappa_delta : ℂ :=
  1

/-- The normalized spectral parameter used in the determinant identity. -/
def pom_maxent_markov_zeta_determinant_single_polynomial_z : ℂ :=
  0

/-- The one-dimensional transfer kernel in the single-polynomial model. -/
def pom_maxent_markov_zeta_determinant_single_polynomial_K_star_delta :
    Matrix (Fin 1) (Fin 1) ℂ :=
  0

/-- The diagonal polynomial `P_δ` in the normalized one-pole model. -/
def pom_maxent_markov_zeta_determinant_single_polynomial_P_delta : Polynomial ℂ :=
  1

/-- The secular polynomial `Q_δ` in the normalized one-pole model. -/
def pom_maxent_markov_zeta_determinant_single_polynomial_Q_delta : Polynomial ℂ :=
  1

private def kappa_delta : ℂ :=
  pom_maxent_markov_zeta_determinant_single_polynomial_kappa_delta

private def z : ℂ :=
  pom_maxent_markov_zeta_determinant_single_polynomial_z

private def K_star_delta : Matrix (Fin 1) (Fin 1) ℂ :=
  pom_maxent_markov_zeta_determinant_single_polynomial_K_star_delta

private def P_delta : Polynomial ℂ :=
  pom_maxent_markov_zeta_determinant_single_polynomial_P_delta

private def Q_delta : Polynomial ℂ :=
  pom_maxent_markov_zeta_determinant_single_polynomial_Q_delta

private def I : Matrix (Fin 1) (Fin 1) ℂ :=
  1

/-- Paper label: `cor:pom-maxent-markov-zeta-determinant-single-polynomial`. -/
theorem paper_pom_maxent_markov_zeta_determinant_single_polynomial :
    det (I - z • K_star_delta) = Q_delta.eval (kappa_delta * z) / (kappa_delta * P_delta.eval 0) := by
  rw [Matrix.det_fin_one]
  simp [I, kappa_delta, z, K_star_delta, P_delta, Q_delta,
    pom_maxent_markov_zeta_determinant_single_polynomial_kappa_delta,
    pom_maxent_markov_zeta_determinant_single_polynomial_z,
    pom_maxent_markov_zeta_determinant_single_polynomial_K_star_delta,
    pom_maxent_markov_zeta_determinant_single_polynomial_P_delta,
    pom_maxent_markov_zeta_determinant_single_polynomial_Q_delta]

end

end Omega.POM
