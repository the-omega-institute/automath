import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete dimension and output-cost data for the Kani-Rosen prime-register package. -/
structure xi_time_part9n1d_prime_register_output_cost_additivity_data where
  xi_time_part9n1d_prime_register_output_cost_additivity_dimJX : Nat
  xi_time_part9n1d_prime_register_output_cost_additivity_dimJH : Nat
  xi_time_part9n1d_prime_register_output_cost_additivity_dimJZ : Nat
  xi_time_part9n1d_prime_register_output_cost_additivity_dimJCF : Nat
  xi_time_part9n1d_prime_register_output_cost_additivity_dimP : Nat
  xi_time_part9n1d_prime_register_output_cost_additivity_rhoJX : Nat
  xi_time_part9n1d_prime_register_output_cost_additivity_rhoJH : Nat
  xi_time_part9n1d_prime_register_output_cost_additivity_rhoJZ : Nat
  xi_time_part9n1d_prime_register_output_cost_additivity_rhoJCF : Nat
  xi_time_part9n1d_prime_register_output_cost_additivity_rhoP : Nat
  xi_time_part9n1d_prime_register_output_cost_additivity_rhoJX_eq :
    xi_time_part9n1d_prime_register_output_cost_additivity_rhoJX =
      2 * xi_time_part9n1d_prime_register_output_cost_additivity_dimJX
  xi_time_part9n1d_prime_register_output_cost_additivity_rhoJH_eq :
    xi_time_part9n1d_prime_register_output_cost_additivity_rhoJH =
      2 * xi_time_part9n1d_prime_register_output_cost_additivity_dimJH
  xi_time_part9n1d_prime_register_output_cost_additivity_rhoJZ_eq :
    xi_time_part9n1d_prime_register_output_cost_additivity_rhoJZ =
      2 * xi_time_part9n1d_prime_register_output_cost_additivity_dimJZ
  xi_time_part9n1d_prime_register_output_cost_additivity_rhoJCF_eq :
    xi_time_part9n1d_prime_register_output_cost_additivity_rhoJCF =
      2 * xi_time_part9n1d_prime_register_output_cost_additivity_dimJCF
  xi_time_part9n1d_prime_register_output_cost_additivity_rhoP_eq :
    xi_time_part9n1d_prime_register_output_cost_additivity_rhoP =
      2 * xi_time_part9n1d_prime_register_output_cost_additivity_dimP
  xi_time_part9n1d_prime_register_output_cost_additivity_dimension_decomposition :
    xi_time_part9n1d_prime_register_output_cost_additivity_dimJX =
      xi_time_part9n1d_prime_register_output_cost_additivity_dimJH +
        2 * xi_time_part9n1d_prime_register_output_cost_additivity_dimJZ +
          3 * xi_time_part9n1d_prime_register_output_cost_additivity_dimJCF +
            3 * xi_time_part9n1d_prime_register_output_cost_additivity_dimP

/-- Strict additivity of the output cost, plus the numerical genus-49 equality. -/
def xi_time_part9n1d_prime_register_output_cost_additivity_statement
    (D : xi_time_part9n1d_prime_register_output_cost_additivity_data) : Prop :=
  D.xi_time_part9n1d_prime_register_output_cost_additivity_rhoJX =
    D.xi_time_part9n1d_prime_register_output_cost_additivity_rhoJH +
      2 * D.xi_time_part9n1d_prime_register_output_cost_additivity_rhoJZ +
        3 * D.xi_time_part9n1d_prime_register_output_cost_additivity_rhoJCF +
          3 * D.xi_time_part9n1d_prime_register_output_cost_additivity_rhoP ∧
    98 = 10 + 2 * 8 + 3 * 6 + 3 * 18

/-- Paper label: `thm:xi-time-part9n1d-prime-register-output-cost-additivity`. -/
theorem paper_xi_time_part9n1d_prime_register_output_cost_additivity
    (D : xi_time_part9n1d_prime_register_output_cost_additivity_data) :
    xi_time_part9n1d_prime_register_output_cost_additivity_statement D := by
  constructor
  · rw [D.xi_time_part9n1d_prime_register_output_cost_additivity_rhoJX_eq,
      D.xi_time_part9n1d_prime_register_output_cost_additivity_rhoJH_eq,
      D.xi_time_part9n1d_prime_register_output_cost_additivity_rhoJZ_eq,
      D.xi_time_part9n1d_prime_register_output_cost_additivity_rhoJCF_eq,
      D.xi_time_part9n1d_prime_register_output_cost_additivity_rhoP_eq,
      D.xi_time_part9n1d_prime_register_output_cost_additivity_dimension_decomposition]
    ring
  · norm_num

end Omega.Zeta
