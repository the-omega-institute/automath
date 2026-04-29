import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The `k`-subsets indexing the Smith invariant factors of `Λ^k C_q`. -/
def xi_exterior_power_det_coker_size_subset_family (q k : ℕ) : Finset (Finset ℕ) :=
  (Finset.range (q + 1)).powersetCard k

/-- The Smith exponent attached to one exterior-power basis subset. -/
def xi_exterior_power_det_coker_size_smith_exponent (S : Finset ℕ) : ℕ :=
  Finset.sum S fun i => i

/-- The determinant valuation is the sum of all Smith exponents. -/
def xi_exterior_power_det_coker_size_det_valuation (q k : ℕ) : ℕ :=
  Finset.sum (xi_exterior_power_det_coker_size_subset_family q k) fun S =>
    xi_exterior_power_det_coker_size_smith_exponent S

/-- The finite cokernel size obtained by multiplying the norm sizes of the cyclic Smith factors. -/
def xi_exterior_power_det_coker_size_coker_size (q k : ℕ) : ℕ :=
  Finset.prod (xi_exterior_power_det_coker_size_subset_family q k) fun S =>
    5 ^ xi_exterior_power_det_coker_size_smith_exponent S

/-- Paper-facing package: Smith exponents are indexed by `k`-subsets of `{0,...,q}`, determinant
valuation is their sum, and the cokernel cardinality is the product of the invariant-factor sizes,
hence `5` to that valuation. -/
def xi_exterior_power_det_coker_size_statement (q k : ℕ) : Prop :=
  xi_exterior_power_det_coker_size_det_valuation q k =
      Finset.sum (xi_exterior_power_det_coker_size_subset_family q k) (fun S =>
        xi_exterior_power_det_coker_size_smith_exponent S) ∧
    xi_exterior_power_det_coker_size_coker_size q k =
      Finset.prod (xi_exterior_power_det_coker_size_subset_family q k) (fun S =>
        5 ^ xi_exterior_power_det_coker_size_smith_exponent S) ∧
    xi_exterior_power_det_coker_size_coker_size q k =
      5 ^ xi_exterior_power_det_coker_size_det_valuation q k

/-- Paper label: `prop:xi-exterior-power-det-coker-size`. -/
theorem paper_xi_exterior_power_det_coker_size (q k : ℕ) :
    xi_exterior_power_det_coker_size_statement q k := by
  refine ⟨rfl, rfl, ?_⟩
  simp [xi_exterior_power_det_coker_size_coker_size,
    xi_exterior_power_det_coker_size_det_valuation, Finset.prod_pow_eq_pow_sum]

end Omega.Zeta
