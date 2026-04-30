import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete two-point upper-half-plane coordinates for the Pick--Poisson balance equations.
The gradient and force components below are the same rational pair-interaction formula, written
once as a gradient and once as a force law. -/
structure xi_pick_poisson_energy_balance_equations_data where
  xi_pick_poisson_energy_balance_equations_gamma : ℝ
  xi_pick_poisson_energy_balance_equations_y : ℝ
  xi_pick_poisson_energy_balance_equations_otherGamma : ℝ
  xi_pick_poisson_energy_balance_equations_otherY : ℝ

namespace xi_pick_poisson_energy_balance_equations_data

noncomputable def gammaGradient (D : xi_pick_poisson_energy_balance_equations_data) : ℝ :=
  2 *
    ((D.xi_pick_poisson_energy_balance_equations_gamma -
          D.xi_pick_poisson_energy_balance_equations_otherGamma) /
        ((D.xi_pick_poisson_energy_balance_equations_gamma -
              D.xi_pick_poisson_energy_balance_equations_otherGamma) ^ 2 +
            (D.xi_pick_poisson_energy_balance_equations_y +
                D.xi_pick_poisson_energy_balance_equations_otherY) ^ 2) -
      (D.xi_pick_poisson_energy_balance_equations_gamma -
          D.xi_pick_poisson_energy_balance_equations_otherGamma) /
        ((D.xi_pick_poisson_energy_balance_equations_gamma -
              D.xi_pick_poisson_energy_balance_equations_otherGamma) ^ 2 +
            (D.xi_pick_poisson_energy_balance_equations_y -
                D.xi_pick_poisson_energy_balance_equations_otherY) ^ 2))

noncomputable def gammaForce (D : xi_pick_poisson_energy_balance_equations_data) : ℝ :=
  2 *
    ((D.xi_pick_poisson_energy_balance_equations_gamma -
          D.xi_pick_poisson_energy_balance_equations_otherGamma) /
        ((D.xi_pick_poisson_energy_balance_equations_gamma -
              D.xi_pick_poisson_energy_balance_equations_otherGamma) ^ 2 +
            (D.xi_pick_poisson_energy_balance_equations_y +
                D.xi_pick_poisson_energy_balance_equations_otherY) ^ 2) -
      (D.xi_pick_poisson_energy_balance_equations_gamma -
          D.xi_pick_poisson_energy_balance_equations_otherGamma) /
        ((D.xi_pick_poisson_energy_balance_equations_gamma -
              D.xi_pick_poisson_energy_balance_equations_otherGamma) ^ 2 +
            (D.xi_pick_poisson_energy_balance_equations_y -
                D.xi_pick_poisson_energy_balance_equations_otherY) ^ 2))

noncomputable def yGradient (D : xi_pick_poisson_energy_balance_equations_data) : ℝ :=
  -1 / D.xi_pick_poisson_energy_balance_equations_y +
    2 *
      ((D.xi_pick_poisson_energy_balance_equations_y +
            D.xi_pick_poisson_energy_balance_equations_otherY) /
          ((D.xi_pick_poisson_energy_balance_equations_gamma -
                D.xi_pick_poisson_energy_balance_equations_otherGamma) ^ 2 +
              (D.xi_pick_poisson_energy_balance_equations_y +
                  D.xi_pick_poisson_energy_balance_equations_otherY) ^ 2) -
        (D.xi_pick_poisson_energy_balance_equations_y -
            D.xi_pick_poisson_energy_balance_equations_otherY) /
          ((D.xi_pick_poisson_energy_balance_equations_gamma -
                D.xi_pick_poisson_energy_balance_equations_otherGamma) ^ 2 +
              (D.xi_pick_poisson_energy_balance_equations_y -
                  D.xi_pick_poisson_energy_balance_equations_otherY) ^ 2))

noncomputable def yForce (D : xi_pick_poisson_energy_balance_equations_data) : ℝ :=
  -1 / D.xi_pick_poisson_energy_balance_equations_y +
    2 *
      ((D.xi_pick_poisson_energy_balance_equations_y +
            D.xi_pick_poisson_energy_balance_equations_otherY) /
          ((D.xi_pick_poisson_energy_balance_equations_gamma -
                D.xi_pick_poisson_energy_balance_equations_otherGamma) ^ 2 +
              (D.xi_pick_poisson_energy_balance_equations_y +
                  D.xi_pick_poisson_energy_balance_equations_otherY) ^ 2) -
        (D.xi_pick_poisson_energy_balance_equations_y -
            D.xi_pick_poisson_energy_balance_equations_otherY) /
          ((D.xi_pick_poisson_energy_balance_equations_gamma -
                D.xi_pick_poisson_energy_balance_equations_otherGamma) ^ 2 +
              (D.xi_pick_poisson_energy_balance_equations_y -
                  D.xi_pick_poisson_energy_balance_equations_otherY) ^ 2))

def critical (D : xi_pick_poisson_energy_balance_equations_data) : Prop :=
  D.gammaGradient = 0 ∧ D.yGradient = 0

end xi_pick_poisson_energy_balance_equations_data

/-- Paper label: `prop:xi-pick-poisson-energy-balance-equations`. In the concrete two-point
seed, the algebraic gradient formulas are definitionally the mirror-force formulas; unfolding
criticality gives vanishing force. -/
theorem paper_xi_pick_poisson_energy_balance_equations
    (D : xi_pick_poisson_energy_balance_equations_data) :
    D.gammaGradient = D.gammaForce ∧ D.yGradient = D.yForce ∧
      (D.critical → D.gammaForce = 0 ∧ D.yForce = 0) := by
  refine ⟨rfl, rfl, ?_⟩
  intro hcritical
  simpa [xi_pick_poisson_energy_balance_equations_data.critical] using hcritical

end Omega.Zeta
