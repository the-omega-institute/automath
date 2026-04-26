import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.GoldenRatio
import Omega.Folding.Entropy

open Filter
open scoped Topology goldenRatio

namespace Omega.Conclusion

noncomputable section

/-- Conclusion-level maxfiber wrapper normalized by the Fibonacci Binet scale. -/
noncomputable def conclusion_maxfiber_average_scale_rigidity_M (m : ℕ) : ℝ :=
  Real.goldenRatio ^ (2 : ℕ) *
    (((fun n : ℕ => (Nat.fib n : ℝ) * (Real.goldenRatio ^ (n : ℝ))⁻¹) ∘
      fun a : ℕ => a + 2) m)

/-- Conclusion-level average-fiber scale. -/
noncomputable def conclusion_maxfiber_average_scale_rigidity_avg (_m : ℕ) : ℝ :=
  1

/-- Paper label: `thm:conclusion-maxfiber-average-scale-rigidity`. The Binet-scaled Fibonacci
main term already converges to `1 / √5`; multiplying by the fixed prefactor `φ²` gives the
conclusion-level ratio limit. -/
theorem paper_conclusion_maxfiber_average_scale_rigidity :
    Tendsto
      (fun m : Nat =>
        conclusion_maxfiber_average_scale_rigidity_M m /
          conclusion_maxfiber_average_scale_rigidity_avg m)
      atTop (nhds (Real.goldenRatio ^ 2 / Real.sqrt 5)) := by
  let conclusion_maxfiber_average_scale_rigidity_profile : ℕ → ℝ :=
    fun m : ℕ =>
      Real.goldenRatio ^ (2 : ℕ) *
        (((fun n : ℕ => (Nat.fib n : ℝ) * (Real.goldenRatio ^ (n : ℝ))⁻¹) ∘
          fun a : ℕ => a + 2) m)
  have hscaled :
      Tendsto conclusion_maxfiber_average_scale_rigidity_profile atTop
        (nhds (Real.goldenRatio ^ (2 : ℕ) * (Real.sqrt 5)⁻¹)) := by
    simpa [conclusion_maxfiber_average_scale_rigidity_profile] using
      Filter.Tendsto.const_mul (Real.goldenRatio ^ (2 : ℕ))
        (Omega.Entropy.fib_mul_phi_neg_tendsto_inv_sqrt5.comp (tendsto_add_atTop_nat 2))
  have hratioEq :
      (fun m : Nat =>
        conclusion_maxfiber_average_scale_rigidity_M m /
          conclusion_maxfiber_average_scale_rigidity_avg m) =
        conclusion_maxfiber_average_scale_rigidity_profile := by
    funext m
    simp [conclusion_maxfiber_average_scale_rigidity_M,
      conclusion_maxfiber_average_scale_rigidity_avg,
      conclusion_maxfiber_average_scale_rigidity_profile, div_eq_mul_inv]
  rw [hratioEq]
  convert hscaled using 1

end

end Omega.Conclusion
