import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.Conclusion

open Filter
open scoped Topology

/-- Collision numerator polynomial `N_{q,T}(z) = 2 + (2^q - 2) z^T`.
The Lean parameter `q` is shifted by two, so all encoded orders satisfy the paper's `q ≥ 2`. -/
noncomputable def conclusion_collision_numerator_regular_polygon_zeros_numerator
    (q T : ℕ) (z : ℂ) : ℂ :=
  2 + (((2 : ℂ) ^ (q + 2)) - 2) * z ^ T

/-- Radius of the regular polygon of roots for the shifted order `q + 2`. -/
noncomputable def conclusion_collision_numerator_regular_polygon_zeros_radius
    (q T : ℕ) : ℝ :=
  (2 / (((2 : ℝ) ^ (q + 2)) - 2)) ^ (1 / (T : ℝ))

def conclusion_collision_numerator_regular_polygon_zeros_statement : Prop :=
  (∀ q T z, 0 < T →
    (conclusion_collision_numerator_regular_polygon_zeros_numerator q T z = 0 ↔
      z ^ T = (-2 : ℂ) / (((2 : ℂ) ^ (q + 2)) - 2))) ∧
    (∀ q, Filter.Tendsto
      (fun T : ℕ => conclusion_collision_numerator_regular_polygon_zeros_radius q (T + 1))
      Filter.atTop (nhds 1))

private lemma conclusion_collision_numerator_regular_polygon_zeros_real_denom_pos
    (q : ℕ) : 0 < ((2 : ℝ) ^ (q + 2)) - 2 := by
  have hpow : (4 : ℝ) ≤ (2 : ℝ) ^ (q + 2) := by
    have hpow' : (2 : ℝ) ^ 2 ≤ (2 : ℝ) ^ (q + 2) :=
      (pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) (show 2 ≤ q + 2 by omega))
    norm_num at hpow'
    exact hpow'
  linarith

private lemma conclusion_collision_numerator_regular_polygon_zeros_complex_denom_ne
    (q : ℕ) : (((2 : ℂ) ^ (q + 2)) - 2) ≠ 0 := by
  have hreal := conclusion_collision_numerator_regular_polygon_zeros_real_denom_pos q
  intro h
  have hcast : (((2 : ℝ) ^ (q + 2) - 2 : ℝ) : ℂ) = 0 := by
    norm_num at h ⊢
    simpa using h
  exact hreal.ne' (Complex.ofReal_injective hcast)

/-- Paper label: `cor:conclusion-collision-numerator-regular-polygon-zeros`. -/
theorem paper_conclusion_collision_numerator_regular_polygon_zeros :
    conclusion_collision_numerator_regular_polygon_zeros_statement := by
  constructor
  · intro q T z _hT
    let c : ℂ := (((2 : ℂ) ^ (q + 2)) - 2)
    have hc : c ≠ 0 :=
      conclusion_collision_numerator_regular_polygon_zeros_complex_denom_ne q
    constructor
    · intro h
      have hmul : c * z ^ T = -2 := by
        dsimp [conclusion_collision_numerator_regular_polygon_zeros_numerator, c] at h ⊢
        linear_combination h
      exact (eq_div_iff hc).2 (by simpa [mul_comm] using hmul)
    · intro h
      dsimp [conclusion_collision_numerator_regular_polygon_zeros_numerator, c] at h ⊢
      calc
        2 + c * z ^ T = 2 + c * ((-2 : ℂ) / c) := by rw [h]
        _ = 0 := by
          field_simp [hc]
          ring
  · intro q
    have hbase_pos : 0 < 2 / (((2 : ℝ) ^ (q + 2)) - 2) := by
      exact div_pos (by norm_num) (conclusion_collision_numerator_regular_polygon_zeros_real_denom_pos q)
    have hpow :
        Filter.Tendsto
          (fun T : ℕ => (2 / (((2 : ℝ) ^ (q + 2)) - 2)) ^ (1 / (T + 1 : ℝ)))
          Filter.atTop (nhds ((2 / (((2 : ℝ) ^ (q + 2)) - 2)) ^ (0 : ℝ))) := by
      exact tendsto_const_nhds.rpow tendsto_one_div_add_atTop_nhds_zero_nat
        (Or.inl hbase_pos.ne')
    simpa [conclusion_collision_numerator_regular_polygon_zeros_radius, Real.rpow_zero,
      Nat.cast_add, Nat.cast_one] using hpow

end Omega.Conclusion
