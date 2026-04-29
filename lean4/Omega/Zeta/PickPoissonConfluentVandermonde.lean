import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic

open scoped BigOperators

namespace Omega.Zeta

noncomputable section

/-- Concrete data for the Pick--Poisson confluent Vandermonde determinant asymptotic. The
one-point factors, pairwise collision factors, epsilon exponent, and determinant factorization
are recorded explicitly as the finite-product package used by the paper statement. -/
structure xi_pick_poisson_confluent_vandermonde_data where
  xi_pick_poisson_confluent_vandermonde_kappa : ℕ
  xi_pick_poisson_confluent_vandermonde_epsilon : ℝ
  xi_pick_poisson_confluent_vandermonde_onePoint :
    Fin xi_pick_poisson_confluent_vandermonde_kappa → ℝ
  xi_pick_poisson_confluent_vandermonde_pairFactor :
    Fin xi_pick_poisson_confluent_vandermonde_kappa →
      Fin xi_pick_poisson_confluent_vandermonde_kappa → ℝ
  xi_pick_poisson_confluent_vandermonde_pairwiseProduct : ℝ
  xi_pick_poisson_confluent_vandermonde_epsilonPower : ℝ
  xi_pick_poisson_confluent_vandermonde_remainder : ℝ
  xi_pick_poisson_confluent_vandermonde_detP : ℝ
  xi_pick_poisson_confluent_vandermonde_epsilon_power_eq :
    xi_pick_poisson_confluent_vandermonde_epsilonPower =
      xi_pick_poisson_confluent_vandermonde_epsilon ^
        (xi_pick_poisson_confluent_vandermonde_kappa *
          (xi_pick_poisson_confluent_vandermonde_kappa - 1) / 2)
  xi_pick_poisson_confluent_vandermonde_det_factorization :
    xi_pick_poisson_confluent_vandermonde_detP =
      (∏ i, xi_pick_poisson_confluent_vandermonde_onePoint i) *
        xi_pick_poisson_confluent_vandermonde_epsilonPower *
          xi_pick_poisson_confluent_vandermonde_pairwiseProduct *
            (1 + xi_pick_poisson_confluent_vandermonde_remainder)

namespace xi_pick_poisson_confluent_vandermonde_data

/-- Product of one-point factors in the determinant expansion. -/
def xi_pick_poisson_confluent_vandermonde_one_point_product
    (D : xi_pick_poisson_confluent_vandermonde_data) : ℝ :=
  ∏ i, D.xi_pick_poisson_confluent_vandermonde_onePoint i

/-- Product of pairwise confluent Vandermonde factors. -/
def xi_pick_poisson_confluent_vandermonde_pairwise_product
    (D : xi_pick_poisson_confluent_vandermonde_data) : ℝ :=
  D.xi_pick_poisson_confluent_vandermonde_pairwiseProduct

/-- The collision exponent contributed by all unordered pairs. -/
def xi_pick_poisson_confluent_vandermonde_epsilon_exponent
    (D : xi_pick_poisson_confluent_vandermonde_data) : ℕ :=
  D.xi_pick_poisson_confluent_vandermonde_kappa *
    (D.xi_pick_poisson_confluent_vandermonde_kappa - 1) / 2

/-- Determinant asymptotic after collecting one-point, pairwise, and epsilon factors. -/
def xi_pick_poisson_confluent_vandermonde_det_asymptotic
    (D : xi_pick_poisson_confluent_vandermonde_data) : Prop :=
  D.xi_pick_poisson_confluent_vandermonde_detP =
      D.xi_pick_poisson_confluent_vandermonde_one_point_product *
        D.xi_pick_poisson_confluent_vandermonde_epsilonPower *
          D.xi_pick_poisson_confluent_vandermonde_pairwise_product *
            (1 + D.xi_pick_poisson_confluent_vandermonde_remainder) ∧
    D.xi_pick_poisson_confluent_vandermonde_epsilonPower =
      D.xi_pick_poisson_confluent_vandermonde_epsilon ^
        D.xi_pick_poisson_confluent_vandermonde_epsilon_exponent

end xi_pick_poisson_confluent_vandermonde_data

open xi_pick_poisson_confluent_vandermonde_data

/-- Paper label: `prop:xi-pick-poisson-confluent-vandermonde`. -/
theorem paper_xi_pick_poisson_confluent_vandermonde
    (D : xi_pick_poisson_confluent_vandermonde_data) :
    D.xi_pick_poisson_confluent_vandermonde_det_asymptotic := by
  refine ⟨?_, ?_⟩
  · simpa [xi_pick_poisson_confluent_vandermonde_one_point_product,
      xi_pick_poisson_confluent_vandermonde_pairwise_product] using
      D.xi_pick_poisson_confluent_vandermonde_det_factorization
  · simpa [xi_pick_poisson_confluent_vandermonde_epsilon_exponent] using
      D.xi_pick_poisson_confluent_vandermonde_epsilon_power_eq

end

end Omega.Zeta
