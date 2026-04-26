import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Omega.POM.DiagonalRateDualPotentialReverseOrder

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- Concrete Robin-Hood transfer data for the audited two-coordinate diagonal-rate model. -/
structure pom_diagonal_rate_robinhood_gain_data where
  heavy : Fin 2
  light : Fin 2
  heavy_eq : heavy = 1
  light_eq : light = 0

/-- Robin-Hood tangent direction `-e_i + e_j`, sending mass from the heavier coordinate to the
lighter one. -/
def pom_diagonal_rate_robinhood_gain_tangent (D : pom_diagonal_rate_robinhood_gain_data)
    (k : Fin 2) : ℝ :=
  if k = D.heavy then -1 else if k = D.light then 1 else 0

/-- Fréchet derivative of the audited diagonal-rate potential in the Robin-Hood direction. -/
noncomputable def pom_diagonal_rate_robinhood_gain_frechet_derivative
    (D : pom_diagonal_rate_robinhood_gain_data) : ℝ :=
  ∑ k : Fin 2,
    pom_diagonal_rate_robinhood_gain_tangent D k *
      pom_diagonal_rate_dual_potential_reverse_order_dual k

/-- Paper-facing positivity package: the explicit reverse-order model has `w_light < w_heavy`,
the Robin-Hood directional derivative is `dual(light) - dual(heavy)`, and this derivative is
strictly positive. -/
def pom_diagonal_rate_robinhood_gain_statement
    (D : pom_diagonal_rate_robinhood_gain_data) : Prop :=
  pom_diagonal_rate_dual_potential_reverse_order_w D.light <
      pom_diagonal_rate_dual_potential_reverse_order_w D.heavy ∧
    pom_diagonal_rate_robinhood_gain_frechet_derivative D =
      pom_diagonal_rate_dual_potential_reverse_order_dual D.light -
        pom_diagonal_rate_dual_potential_reverse_order_dual D.heavy ∧
    0 < pom_diagonal_rate_robinhood_gain_frechet_derivative D

/-- Paper label: `prop:pom-diagonal-rate-robinhood-gain`. In the explicit audited two-point model,
the reverse-order dual potential makes the Robin-Hood derivative along `-e_heavy + e_light`
equal to `dual(light) - dual(heavy)`, hence strictly positive because `w_heavy > w_light`
forces `dual(heavy) < dual(light)`. -/
theorem paper_pom_diagonal_rate_robinhood_gain
    (D : pom_diagonal_rate_robinhood_gain_data) : pom_diagonal_rate_robinhood_gain_statement D := by
  rcases D with ⟨heavy, light, rfl, rfl⟩
  rcases paper_pom_diagonal_rate_dual_potential_reverse_order with
    ⟨_, _, hw01, hdual10, _, _⟩
  have hderiv :
      pom_diagonal_rate_robinhood_gain_frechet_derivative
          { heavy := 1, light := 0, heavy_eq := rfl, light_eq := rfl } =
        pom_diagonal_rate_dual_potential_reverse_order_dual 0 -
          pom_diagonal_rate_dual_potential_reverse_order_dual 1 := by
    simp [pom_diagonal_rate_robinhood_gain_frechet_derivative,
      pom_diagonal_rate_robinhood_gain_tangent, sub_eq_add_neg]
  refine ⟨hw01, hderiv, ?_⟩
  rw [hderiv]
  exact sub_pos.mpr hdual10

end

end Omega.POM
