import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete data for `cor:xi-poisson-kl-l1-square-equivalence-first-moment`.

Both asymptotic constants factor through the same first moment, and the remaining
second-order constants are related by the explicit quadratic equivalence constant. -/
structure xi_poisson_kl_l1_square_equivalence_first_moment_Data where
  xi_poisson_kl_l1_square_equivalence_first_moment_commonFirstMoment : ℝ
  xi_poisson_kl_l1_square_equivalence_first_moment_klSecondOrderConstant : ℝ
  xi_poisson_kl_l1_square_equivalence_first_moment_l1SquaredSecondOrderConstant : ℝ
  xi_poisson_kl_l1_square_equivalence_first_moment_explicitQuadraticConstant : ℝ
  xi_poisson_kl_l1_square_equivalence_first_moment_secondOrderConstant_eq :
    xi_poisson_kl_l1_square_equivalence_first_moment_klSecondOrderConstant =
      xi_poisson_kl_l1_square_equivalence_first_moment_l1SquaredSecondOrderConstant *
        xi_poisson_kl_l1_square_equivalence_first_moment_explicitQuadraticConstant

namespace xi_poisson_kl_l1_square_equivalence_first_moment_Data

/-- KL asymptotic constant after factoring the common first moment. -/
def klAsymptoticConstant
    (D : xi_poisson_kl_l1_square_equivalence_first_moment_Data) : ℝ :=
  D.xi_poisson_kl_l1_square_equivalence_first_moment_commonFirstMoment *
    D.xi_poisson_kl_l1_square_equivalence_first_moment_klSecondOrderConstant

/-- Squared `L1` asymptotic constant after factoring the common first moment. -/
def l1SquaredAsymptoticConstant
    (D : xi_poisson_kl_l1_square_equivalence_first_moment_Data) : ℝ :=
  D.xi_poisson_kl_l1_square_equivalence_first_moment_commonFirstMoment *
    D.xi_poisson_kl_l1_square_equivalence_first_moment_l1SquaredSecondOrderConstant

/-- Explicit constant relating the two second-order limits. -/
def explicitConstant
    (D : xi_poisson_kl_l1_square_equivalence_first_moment_Data) : ℝ :=
  D.xi_poisson_kl_l1_square_equivalence_first_moment_explicitQuadraticConstant

end xi_poisson_kl_l1_square_equivalence_first_moment_Data

open xi_poisson_kl_l1_square_equivalence_first_moment_Data

/-- Paper label: `cor:xi-poisson-kl-l1-square-equivalence-first-moment`. -/
theorem paper_xi_poisson_kl_l1_square_equivalence_first_moment
    (D : xi_poisson_kl_l1_square_equivalence_first_moment_Data) :
    D.klAsymptoticConstant = D.l1SquaredAsymptoticConstant * D.explicitConstant := by
  unfold klAsymptoticConstant l1SquaredAsymptoticConstant explicitConstant
  rw [D.xi_poisson_kl_l1_square_equivalence_first_moment_secondOrderConstant_eq]
  ring

end Omega.Zeta
