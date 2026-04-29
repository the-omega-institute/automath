import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Primitive length-two coordinate contributed by the atomic Witt factor `(1 - u z^2)^{-1}`. -/
def conclusion_atomic_witt_factor_quantized_abel_shift_primitive (u : ℝ) (n : ℕ) : ℝ :=
  if n = 2 then u else 0

/-- Concrete statement for `prop:conclusion-atomic-witt-factor-quantized-abel-shift`. -/
def conclusion_atomic_witt_factor_quantized_abel_shift_statement : Prop :=
  (∀ u : ℝ,
      conclusion_atomic_witt_factor_quantized_abel_shift_primitive u 2 = u ∧
        ∀ n : ℕ, n ≠ 2 →
          conclusion_atomic_witt_factor_quantized_abel_shift_primitive u n = 0) ∧
    (∀ z pCore logCore : ℝ,
      (1 : ℝ) * z ^ (2 : ℕ) + pCore = z ^ (2 : ℕ) + pCore ∧
        logCore + (Real.goldenRatio⁻¹ : ℝ) ^ (4 : ℕ) =
          logCore + (7 - 3 * Real.sqrt 5) / 2) ∧
    ((Real.goldenRatio⁻¹ : ℝ) ^ (4 : ℕ) = (7 - 3 * Real.sqrt 5) / 2)

lemma conclusion_atomic_witt_factor_quantized_abel_shift_golden_inv_four :
    (Real.goldenRatio⁻¹ : ℝ) ^ (4 : ℕ) = (7 - 3 * Real.sqrt 5) / 2 := by
  rw [Real.inv_goldenRatio]
  unfold Real.goldenConj
  have hsqrt5_sq : (Real.sqrt 5 : ℝ) ^ (2 : ℕ) = 5 := by
    exact Real.sq_sqrt (by norm_num)
  have hsqrt5_cube : (Real.sqrt 5 : ℝ) ^ (3 : ℕ) = 5 * Real.sqrt 5 := by
    calc
      (Real.sqrt 5 : ℝ) ^ (3 : ℕ) = (Real.sqrt 5 : ℝ) ^ (2 : ℕ) * Real.sqrt 5 := by
        ring
      _ = 5 * Real.sqrt 5 := by rw [hsqrt5_sq]
  have hsqrt5_four : (Real.sqrt 5 : ℝ) ^ (4 : ℕ) = 25 := by
    calc
      (Real.sqrt 5 : ℝ) ^ (4 : ℕ) = ((Real.sqrt 5 : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ) := by
        ring
      _ = 25 := by rw [hsqrt5_sq]; norm_num
  ring_nf
  nlinarith [hsqrt5_sq, hsqrt5_cube, hsqrt5_four]

/-- Paper label: `prop:conclusion-atomic-witt-factor-quantized-abel-shift`. -/
theorem paper_conclusion_atomic_witt_factor_quantized_abel_shift :
    conclusion_atomic_witt_factor_quantized_abel_shift_statement := by
  refine ⟨?_, ?_, conclusion_atomic_witt_factor_quantized_abel_shift_golden_inv_four⟩
  · intro u
    constructor
    · simp [conclusion_atomic_witt_factor_quantized_abel_shift_primitive]
    · intro n hn
      simp [conclusion_atomic_witt_factor_quantized_abel_shift_primitive, hn]
  · intro z pCore logCore
    constructor
    · ring
    · rw [conclusion_atomic_witt_factor_quantized_abel_shift_golden_inv_four]

end Omega.Conclusion
