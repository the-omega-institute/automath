import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.FoldZeroWindow6DensitySharpExponent

open Filter
open scoped Topology goldenRatio

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-half-entropy-forbidden-band`.
On the rigid window-`6` subsequence `m = 6n + 4`, the half-index zero-frequency lower bound
already formalized in the folding chapter gives a visible Fibonacci block of forbidden
frequencies; the corresponding normalized logarithmic lower-bound model has limiting slope
`(1 / 2) log φ`. -/
theorem paper_conclusion_half_entropy_forbidden_band :
    (∀ n : ℕ, Nat.fib (3 * n + 3) ≤ (Omega.Folding.foldZeroFrequencyUnion (6 * n + 4)).card) ∧
      Tendsto
        (fun n : ℕ => Real.log (Nat.fib (3 * n + 3) : ℝ) / ((6 * n + 4 : ℕ) : ℝ))
        atTop (𝓝 ((1 / 2 : ℝ) * Real.log Real.goldenRatio)) := by
  have hwindow := Omega.Folding.paper_fold_zero_window6_density_sharp_exponent
  refine ⟨hwindow.1, ?_⟩
  have hmain :
      Tendsto (fun n : ℕ => Real.log (Nat.fib (3 * n + 3) : ℝ) / ((3 * n + 1 : ℕ) : ℝ)) atTop
        (𝓝 (Real.log Real.goldenRatio)) :=
    hwindow.2.2.1
  have hinv :
      Tendsto (fun n : ℕ => (((3 * n + 2 : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) := by
    have hbase :
        Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hshift :
        Tendsto (fun n : ℕ => (1 / (((3 * n + 1 : ℕ) : ℝ) + 1) : ℝ)) atTop (𝓝 0) := by
      refine hbase.comp ?_
      refine tendsto_atTop.2 ?_
      intro b
      filter_upwards [Filter.eventually_ge_atTop b] with n hn
      omega
    have hEq :
        (fun n : ℕ => (1 / (((3 * n + 1 : ℕ) : ℝ) + 1) : ℝ)) =
          fun n : ℕ => (((3 * n + 2 : ℕ) : ℝ)⁻¹) := by
      funext n
      have hcast : ((((3 * n + 1 : ℕ) : ℝ) + 1)) = ((3 * n + 2 : ℕ) : ℝ) := by
        exact_mod_cast (show 3 * n + 1 + 1 = 3 * n + 2 by omega)
      rw [hcast, one_div]
    rw [hEq] at hshift
    exact hshift
  have hratio :
      Tendsto (fun n : ℕ => ((3 * n + 1 : ℕ) : ℝ) / ((6 * n + 4 : ℕ) : ℝ)) atTop
        (𝓝 (1 / 2 : ℝ)) := by
    have hEq :
        (fun n : ℕ => ((3 * n + 1 : ℕ) : ℝ) / ((6 * n + 4 : ℕ) : ℝ)) =
          fun n : ℕ => (1 / 2 : ℝ) - (((3 * n + 2 : ℕ) : ℝ)⁻¹) / 2 := by
      funext n
      have hden : (((6 * n + 4 : ℕ) : ℝ)) ≠ 0 := by positivity
      field_simp [hden]
      norm_num [Nat.cast_add, Nat.cast_mul, add_assoc, add_comm, add_left_comm]
      ring
    rw [hEq]
    simpa [div_eq_mul_inv] using (tendsto_const_nhds.sub (hinv.div_const 2))
  have hEq :
      (fun n : ℕ => Real.log (Nat.fib (3 * n + 3) : ℝ) / ((6 * n + 4 : ℕ) : ℝ)) =
        fun n : ℕ =>
          (Real.log (Nat.fib (3 * n + 3) : ℝ) / ((3 * n + 1 : ℕ) : ℝ)) *
            (((3 * n + 1 : ℕ) : ℝ) / ((6 * n + 4 : ℕ) : ℝ)) := by
    funext n
    have hmid : (((3 * n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    have hden : (((6 * n + 4 : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp [hmid, hden]
  rw [hEq]
  have hmul := hmain.mul hratio
  simpa [mul_assoc, mul_comm, mul_left_comm] using hmul

end Omega.Conclusion
