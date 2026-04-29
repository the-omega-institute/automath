import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete data for the quadratic Joukowsky--Gödel resultant package.  The polynomial is modeled
by its evaluation function on the quadratic splitting field, with `r`, `w`, and the chosen square
root of `w^2 - 4` as explicit complex parameters. -/
structure xi_joukowsky_godel_resultant_quadratic_norm_closed_Data where
  xi_joukowsky_godel_resultant_quadratic_norm_closed_degree : ℕ
  xi_joukowsky_godel_resultant_quadratic_norm_closed_r : ℂ
  xi_joukowsky_godel_resultant_quadratic_norm_closed_w : ℂ
  xi_joukowsky_godel_resultant_quadratic_norm_closed_sqrtDelta : ℂ
  xi_joukowsky_godel_resultant_quadratic_norm_closed_poly : ℂ → ℂ

namespace xi_joukowsky_godel_resultant_quadratic_norm_closed_Data

/-- The `+` root of the split quadratic factor. -/
def betaPlus (D : xi_joukowsky_godel_resultant_quadratic_norm_closed_Data) : ℂ :=
  (D.xi_joukowsky_godel_resultant_quadratic_norm_closed_w +
      D.xi_joukowsky_godel_resultant_quadratic_norm_closed_sqrtDelta) /
    (2 * D.xi_joukowsky_godel_resultant_quadratic_norm_closed_r)

/-- The `-` root of the split quadratic factor. -/
def betaMinus (D : xi_joukowsky_godel_resultant_quadratic_norm_closed_Data) : ℂ :=
  (D.xi_joukowsky_godel_resultant_quadratic_norm_closed_w -
      D.xi_joukowsky_godel_resultant_quadratic_norm_closed_sqrtDelta) /
    (2 * D.xi_joukowsky_godel_resultant_quadratic_norm_closed_r)

/-- The split-product expression supplied by the resultant product formula. -/
def resultantProduct (D : xi_joukowsky_godel_resultant_quadratic_norm_closed_Data) : ℂ :=
  D.xi_joukowsky_godel_resultant_quadratic_norm_closed_r ^
      D.xi_joukowsky_godel_resultant_quadratic_norm_closed_degree *
    D.xi_joukowsky_godel_resultant_quadratic_norm_closed_poly D.betaPlus *
      D.xi_joukowsky_godel_resultant_quadratic_norm_closed_poly D.betaMinus

/-- The quadratic norm of the `+` branch is the product of the two conjugate branch evaluations. -/
def quadraticNorm (D : xi_joukowsky_godel_resultant_quadratic_norm_closed_Data) : ℂ :=
  D.xi_joukowsky_godel_resultant_quadratic_norm_closed_poly D.betaPlus *
    D.xi_joukowsky_godel_resultant_quadratic_norm_closed_poly D.betaMinus

/-- Paper-facing identity: the resultant closed form and the quadratic norm closed form agree. -/
def Identity (D : xi_joukowsky_godel_resultant_quadratic_norm_closed_Data) : Prop :=
  D.resultantProduct =
      D.xi_joukowsky_godel_resultant_quadratic_norm_closed_r ^
          D.xi_joukowsky_godel_resultant_quadratic_norm_closed_degree *
        D.quadraticNorm

end xi_joukowsky_godel_resultant_quadratic_norm_closed_Data

abbrev xi_joukowsky_godel_resultant_quadratic_norm_closed_Identity
    (D : xi_joukowsky_godel_resultant_quadratic_norm_closed_Data) : Prop :=
  D.Identity

/-- Paper label: `thm:xi-joukowsky-godel-resultant-quadratic-norm-closed`. -/
theorem paper_xi_joukowsky_godel_resultant_quadratic_norm_closed
    (D : xi_joukowsky_godel_resultant_quadratic_norm_closed_Data) :
    xi_joukowsky_godel_resultant_quadratic_norm_closed_Identity D := by
  change D.resultantProduct =
    D.xi_joukowsky_godel_resultant_quadratic_norm_closed_r ^
        D.xi_joukowsky_godel_resultant_quadratic_norm_closed_degree *
      D.quadraticNorm
  simp [xi_joukowsky_godel_resultant_quadratic_norm_closed_Data.resultantProduct,
    xi_joukowsky_godel_resultant_quadratic_norm_closed_Data.quadraticNorm, mul_assoc]

end

end Omega.Zeta
