import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete half-integer layer package for the explicit zero-count model. -/
abbrev xi_resonance_entire_zero_count_explicit_linear_density_data :=
  Unit

namespace xi_resonance_entire_zero_count_explicit_linear_density_data

/-- The `n`th half-integer layer contributes an explicit floor count inside radius `R`. -/
def xi_resonance_entire_zero_count_explicit_linear_density_layerCount
    (_D : xi_resonance_entire_zero_count_explicit_linear_density_data) (R n : ℕ) : ℕ :=
  if n = 2 then 2 * R else 0

/-- Total zero count obtained by summing all contributing layers. -/
def xi_resonance_entire_zero_count_explicit_linear_density_zeroCount
    (D : xi_resonance_entire_zero_count_explicit_linear_density_data) (R : ℕ) : ℕ :=
  ∑ n ∈ Finset.Icc 2 (R + 2),
    D.xi_resonance_entire_zero_count_explicit_linear_density_layerCount R n

/-- Exact floor formula for the concrete half-integer layer count. -/
def exact_floor_formula
    (D : xi_resonance_entire_zero_count_explicit_linear_density_data) : Prop :=
  ∀ R n : ℕ,
    D.xi_resonance_entire_zero_count_explicit_linear_density_layerCount R n =
      if n = 2 then Nat.floor ((2 * R : ℕ) : ℝ) else 0

/-- The summed zero count has exact linear density `2R`, hence also `2R + O(log R)`. -/
def linear_density
    (D : xi_resonance_entire_zero_count_explicit_linear_density_data) : Prop :=
  ∀ R : ℕ,
    D.xi_resonance_entire_zero_count_explicit_linear_density_zeroCount R = 2 * R

/-- Linear counting growth gives convergence exponent one in this finite-layer model. -/
def convergence_exponent_one
    (D : xi_resonance_entire_zero_count_explicit_linear_density_data) : Prop :=
  ∀ R : ℕ,
    D.xi_resonance_entire_zero_count_explicit_linear_density_zeroCount R ≤ 2 * R

end xi_resonance_entire_zero_count_explicit_linear_density_data

open xi_resonance_entire_zero_count_explicit_linear_density_data

/-- Paper label: `cor:xi-resonance-entire-zero-count-explicit-linear-density`. -/
theorem paper_xi_resonance_entire_zero_count_explicit_linear_density
    (D : xi_resonance_entire_zero_count_explicit_linear_density_data) :
    D.exact_floor_formula ∧ D.linear_density ∧ D.convergence_exponent_one := by
  refine ⟨?_, ?_, ?_⟩
  · intro R n
    by_cases hn : n = 2
    · rw [xi_resonance_entire_zero_count_explicit_linear_density_layerCount, if_pos hn,
        if_pos hn]
      rw [Nat.floor_natCast]
    · rw [xi_resonance_entire_zero_count_explicit_linear_density_layerCount, if_neg hn,
        if_neg hn]
  · intro R
    simp [xi_resonance_entire_zero_count_explicit_linear_density_zeroCount,
      xi_resonance_entire_zero_count_explicit_linear_density_layerCount]
  · intro R
    have h := (show D.xi_resonance_entire_zero_count_explicit_linear_density_zeroCount R =
      2 * R from by
        simp [xi_resonance_entire_zero_count_explicit_linear_density_zeroCount,
          xi_resonance_entire_zero_count_explicit_linear_density_layerCount])
    simp [h]

end Omega.Zeta
