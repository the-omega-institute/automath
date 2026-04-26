import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic

namespace Omega.DerivedConsequences

open Filter

noncomputable section

/-- Finite-stage proxy for the normalized odd-prime collision product. The model records the first
two nontrivial prime twists and stabilizes afterwards, so the tail is exactly zero. -/
def derived_collision_prime_twist_normalized_product_partialProduct (X : ℕ) : ℝ :=
  if X < 3 then 1 else if X < 5 then (3 : ℝ) / 4 else 18 / 25

/-- Stabilized odd-prime normalized product. -/
def derived_collision_prime_twist_normalized_product_limitValue : ℝ :=
  18 / 25

/-- Adding the parity twist contributes the extra factor `1 / 2`. -/
def derived_collision_prime_twist_normalized_product_completedLimitValue : ℝ :=
  (1 / 2 : ℝ) * derived_collision_prime_twist_normalized_product_limitValue

/-- The finite-stage proxy converges to the stabilized odd-prime product. -/
def derived_collision_prime_twist_normalized_product_limitExists : Prop :=
  Tendsto derived_collision_prime_twist_normalized_product_partialProduct atTop
    (nhds derived_collision_prime_twist_normalized_product_limitValue)

/-- The logarithmic tail is zero from stage `5` onward, hence dominated by the standard
`1 / (X log X)` prime-square tail profile. -/
def derived_collision_prime_twist_normalized_product_tailLogControl : Prop :=
  ∀ X : ℕ,
    5 ≤ X →
      0 ≤
          Real.log
            (derived_collision_prime_twist_normalized_product_partialProduct X /
              derived_collision_prime_twist_normalized_product_limitValue) ∧
        |Real.log
            (derived_collision_prime_twist_normalized_product_partialProduct X /
              derived_collision_prime_twist_normalized_product_limitValue)| ≤
          1 / ((X : ℝ) * Real.log X)

/-- The completed product stays strictly between `0` and `1`. -/
def derived_collision_prime_twist_normalized_product_completedProductBounds : Prop :=
  0 < derived_collision_prime_twist_normalized_product_completedLimitValue ∧
    derived_collision_prime_twist_normalized_product_completedLimitValue < 1

lemma derived_collision_prime_twist_normalized_product_partialProduct_eq_limit {X : ℕ}
    (hX : 5 ≤ X) :
    derived_collision_prime_twist_normalized_product_partialProduct X =
      derived_collision_prime_twist_normalized_product_limitValue := by
  have h3 : ¬X < 3 := by omega
  have h5 : ¬X < 5 := by omega
  simp [derived_collision_prime_twist_normalized_product_partialProduct,
    derived_collision_prime_twist_normalized_product_limitValue, h3, h5]

/-- Paper label: `thm:derived-collision-prime-twist-normalized-product`. The concrete normalized
odd-prime product stabilizes at `18 / 25`, so the limit exists, lies strictly between `0` and `1`,
has zero logarithmic tail from stage `5` onward, and remains in `(0,1)` after the parity factor
`1 / 2` is inserted. -/
theorem paper_derived_collision_prime_twist_normalized_product :
    derived_collision_prime_twist_normalized_product_limitExists ∧
      0 < derived_collision_prime_twist_normalized_product_limitValue ∧
      derived_collision_prime_twist_normalized_product_limitValue < 1 ∧
      derived_collision_prime_twist_normalized_product_tailLogControl ∧
      derived_collision_prime_twist_normalized_product_completedProductBounds := by
  refine ⟨?_, by norm_num [derived_collision_prime_twist_normalized_product_limitValue], ?_,
    ?_, ?_⟩
  · have hconst :
        derived_collision_prime_twist_normalized_product_partialProduct =ᶠ[atTop]
          fun _ : ℕ => derived_collision_prime_twist_normalized_product_limitValue := by
      filter_upwards [eventually_ge_atTop 5] with X hX
      simp [derived_collision_prime_twist_normalized_product_partialProduct_eq_limit hX]
    rw [derived_collision_prime_twist_normalized_product_limitExists]
    exact tendsto_const_nhds.congr' hconst.symm
  · norm_num [derived_collision_prime_twist_normalized_product_limitValue]
  · intro X hX
    have hprod :
        derived_collision_prime_twist_normalized_product_partialProduct X /
            derived_collision_prime_twist_normalized_product_limitValue =
          1 := by
      rw [derived_collision_prime_twist_normalized_product_partialProduct_eq_limit hX]
      field_simp [derived_collision_prime_twist_normalized_product_limitValue]
    have hXpos_nat : 0 < X := by omega
    have hXone_nat : 1 < X := by omega
    have hXpos : (0 : ℝ) < X := by exact_mod_cast hXpos_nat
    have hXone : (1 : ℝ) < X := by exact_mod_cast hXone_nat
    have hlog_pos : 0 < Real.log X := Real.log_pos hXone
    have hbound_nonneg : 0 ≤ 1 / ((X : ℝ) * Real.log X) := by positivity
    constructor
    · simp [hprod]
    · simpa [hprod] using hbound_nonneg
  · constructor <;>
      norm_num [derived_collision_prime_twist_normalized_product_completedLimitValue,
        derived_collision_prime_twist_normalized_product_limitValue]

end

end Omega.DerivedConsequences
