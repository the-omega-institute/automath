import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Omega.Folding

open scoped BigOperators

/-- Weighted Cauchy-Schwarz turns the coordinate bias/readout pairing into a square-root bound once
the weighted bias energy is controlled.
    thm:fold-hypercube-godel-length-energy-upperbound -/
theorem paper_fold_hypercube_godel_length_energy_upperbound (n : Nat) (bias w logq : Fin n → ℝ)
    (E : ℝ) (hpos : ∀ i, 0 < w i)
    (henergy : (∑ i, w i * (bias i)^2) ≤ (2 : ℝ)^(n - 1) * E) :
    (∑ i, |bias i| * logq i) ≤
      Real.sqrt ((2 : ℝ)^(n - 1) * E) * Real.sqrt (∑ i, (logq i)^2 / w i) := by
  have hCauchy :
      (∑ i, (Real.sqrt (w i) * |bias i|) * (logq i / Real.sqrt (w i))) ≤
        Real.sqrt (∑ i, (Real.sqrt (w i) * |bias i|)^2) *
          Real.sqrt (∑ i, (logq i / Real.sqrt (w i))^2) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      Real.sum_mul_le_sqrt_mul_sqrt
        (Finset.univ : Finset (Fin n))
        (fun i : Fin n => Real.sqrt (w i) * |bias i|)
        (fun i : Fin n => logq i / Real.sqrt (w i))
  have hlhs :
      (∑ i, (Real.sqrt (w i) * |bias i|) * (logq i / Real.sqrt (w i))) =
        ∑ i, |bias i| * logq i := by
    refine Finset.sum_congr rfl ?_
    intro i _
    have hsqrt_ne : Real.sqrt (w i) ≠ 0 := by
      exact ne_of_gt (Real.sqrt_pos.2 (hpos i))
    field_simp [hsqrt_ne]
  have hxsq :
      (∑ i, (Real.sqrt (w i) * |bias i|)^2) = ∑ i, w i * (bias i)^2 := by
    refine Finset.sum_congr rfl ?_
    intro i _
    calc
      (Real.sqrt (w i) * |bias i|)^2 = (Real.sqrt (w i))^2 * |bias i|^2 := by ring
      _ = w i * (bias i)^2 := by rw [Real.sq_sqrt (le_of_lt (hpos i)), sq_abs]
  have hysq :
      (∑ i, (logq i / Real.sqrt (w i))^2) = ∑ i, (logq i)^2 / w i := by
    refine Finset.sum_congr rfl ?_
    intro i _
    have hsqrt_ne : Real.sqrt (w i) ≠ 0 := by
      exact ne_of_gt (Real.sqrt_pos.2 (hpos i))
    calc
      (logq i / Real.sqrt (w i))^2 = (logq i)^2 / (Real.sqrt (w i))^2 := by
        field_simp [hsqrt_ne]
      _ = (logq i)^2 / w i := by rw [Real.sq_sqrt (le_of_lt (hpos i))]
  calc
    ∑ i, |bias i| * logq i
        = ∑ i, (Real.sqrt (w i) * |bias i|) * (logq i / Real.sqrt (w i)) := hlhs.symm
    _ ≤ Real.sqrt (∑ i, (Real.sqrt (w i) * |bias i|)^2) *
          Real.sqrt (∑ i, (logq i / Real.sqrt (w i))^2) := hCauchy
    _ = Real.sqrt (∑ i, w i * (bias i)^2) * Real.sqrt (∑ i, (logq i)^2 / w i) := by
          rw [hxsq, hysq]
    _ ≤ Real.sqrt ((2 : ℝ)^(n - 1) * E) * Real.sqrt (∑ i, (logq i)^2 / w i) := by
          exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt henergy) (Real.sqrt_nonneg _)

end Omega.Folding
