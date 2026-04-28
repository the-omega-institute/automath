import Mathlib.Tactic

namespace Omega.Zeta

/-- Tame local Artin conductor exponent `dim rho - dim rho^I`. -/
def xi_p7_s5_global_artin_conductors_rho456_local_conductor_exponent
    (dimension fixedDimension : ℕ) : ℕ :=
  dimension - fixedDimension

/-- The global conductor assembled from dyadic and odd-prime local exponents. -/
def xi_p7_s5_global_artin_conductors_rho456_global_conductor
    (q dyadicExponent oddExponent : ℕ) : ℕ :=
  2 ^ dyadicExponent * q ^ oddExponent

/-- The three Artin conductors for `rho4`, `rho5`, and `rho6`.  The dyadic fixed dimensions are
`(2, 1, 2)` for `C3` inertia, while the odd-prime fixed dimensions are all `3` for `C2`
inertia. -/
def xi_p7_s5_global_artin_conductors_rho456_conductors
    (q : ℕ) : ℕ × ℕ × ℕ :=
  (xi_p7_s5_global_artin_conductors_rho456_global_conductor q
      (xi_p7_s5_global_artin_conductors_rho456_local_conductor_exponent 4 2)
      (xi_p7_s5_global_artin_conductors_rho456_local_conductor_exponent 4 3),
    xi_p7_s5_global_artin_conductors_rho456_global_conductor q
      (xi_p7_s5_global_artin_conductors_rho456_local_conductor_exponent 5 1)
      (xi_p7_s5_global_artin_conductors_rho456_local_conductor_exponent 5 3),
    xi_p7_s5_global_artin_conductors_rho456_global_conductor q
      (xi_p7_s5_global_artin_conductors_rho456_local_conductor_exponent 6 2)
      (xi_p7_s5_global_artin_conductors_rho456_local_conductor_exponent 6 3))

/-- Paper label: `thm:xi-p7-s5-global-artin-conductors-rho456`. -/
theorem paper_xi_p7_s5_global_artin_conductors_rho456 (q : ℕ) :
    xi_p7_s5_global_artin_conductors_rho456_conductors q =
      (2 ^ 2 * q, 2 ^ 4 * q ^ 2, 2 ^ 4 * q ^ 3) := by
  simp [xi_p7_s5_global_artin_conductors_rho456_conductors,
    xi_p7_s5_global_artin_conductors_rho456_global_conductor,
    xi_p7_s5_global_artin_conductors_rho456_local_conductor_exponent]

end Omega.Zeta
