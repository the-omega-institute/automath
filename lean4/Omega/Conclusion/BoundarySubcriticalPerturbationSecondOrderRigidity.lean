import Mathlib
import Omega.SPG.GodelDoublelogMinkowski

namespace Omega.Conclusion

open Filter

/-- The dyadic main scale `2^{m d}` appearing in the second-order counting asymptotic. -/
noncomputable def conclusion_boundary_subcritical_perturbation_second_order_rigidity_scale
    (d m : ℕ) : ℝ :=
  (2 : ℝ) ^ (m * d)

/-- Dyadic counting function `N_m = 2^{m n} Vol(V_m)` attached to a volume profile. -/
noncomputable def conclusion_boundary_subcritical_perturbation_second_order_rigidity_count
    (n : ℕ) (vol : ℕ → ℝ) (m : ℕ) : ℝ :=
  (2 : ℝ) ^ (m * n) * vol m

/-- The second-order dyadic Minkowski asymptotic `N_m = M 2^{m d} + o(2^{m d})`, recorded as the
normalized error tending to `0`. -/
def conclusion_boundary_subcritical_perturbation_second_order_rigidity_has_asymptotic
    (count : ℕ → ℝ) (d : ℕ) (M : ℝ) : Prop :=
  Tendsto
    (fun m =>
      (count m -
          M * conclusion_boundary_subcritical_perturbation_second_order_rigidity_scale d m) /
        conclusion_boundary_subcritical_perturbation_second_order_rigidity_scale d m)
    atTop (nhds 0)

set_option maxHeartbeats 400000 in
/-- After multiplying the SPG Lipschitz volume bound by `2^{m n}`, any subcritical boundary error
whose normalized size tends to `0` preserves the full second-order dyadic counting asymptotic, and
hence preserves the same dyadic Minkowski dimension/content package.
    thm:conclusion-boundary-subcritical-perturbation-second-order-rigidity -/
theorem paper_conclusion_boundary_subcritical_perturbation_second_order_rigidity
    (n d : ℕ) (M : ℝ) (volA volV : ℕ → ℝ) (boundaryError : ℕ → ℝ)
    (hA :
      conclusion_boundary_subcritical_perturbation_second_order_rigidity_has_asymptotic
        (conclusion_boundary_subcritical_perturbation_second_order_rigidity_count n volA) d M)
    (hGap :
      ∀ m,
        |conclusion_boundary_subcritical_perturbation_second_order_rigidity_count n volV m -
            conclusion_boundary_subcritical_perturbation_second_order_rigidity_count n volA m| ≤
          conclusion_boundary_subcritical_perturbation_second_order_rigidity_scale d m *
            |boundaryError m|)
    (hBoundary : Tendsto boundaryError atTop (nhds 0))
    (hMpos : 0 < M) :
    conclusion_boundary_subcritical_perturbation_second_order_rigidity_has_asymptotic
        (conclusion_boundary_subcritical_perturbation_second_order_rigidity_count n volV) d M ∧
      0 < M := by
  let scale :=
    conclusion_boundary_subcritical_perturbation_second_order_rigidity_scale d
  let countA :=
    conclusion_boundary_subcritical_perturbation_second_order_rigidity_count n volA
  let countV :=
    conclusion_boundary_subcritical_perturbation_second_order_rigidity_count n volV
  let gap := fun m => (countV m - countA m) / scale m
  let main := fun m => (countA m - M * scale m) / scale m
  have hBoundaryAbs : Tendsto (fun m => |boundaryError m|) atTop (nhds 0) := by
    simpa using (tendsto_zero_iff_abs_tendsto_zero boundaryError).1 hBoundary
  have hGapAbsLe : ∀ m, |gap m| ≤ |boundaryError m| := by
    intro m
    have hscale_pos : 0 < scale m := by
      dsimp [scale, conclusion_boundary_subcritical_perturbation_second_order_rigidity_scale]
      positivity
    have hdiv :
        |countV m - countA m| / scale m ≤ |boundaryError m| := by
      exact (_root_.div_le_iff₀ hscale_pos).2 (by simpa [mul_comm] using hGap m)
    simpa [gap, abs_div, abs_of_pos hscale_pos] using hdiv
  have hGapTendsto : Tendsto gap atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    exact squeeze_zero (fun m => abs_nonneg _) hGapAbsLe hBoundaryAbs
  have hMainTendsto : Tendsto main atTop (nhds 0) := by
    simpa [main, countA, scale,
      conclusion_boundary_subcritical_perturbation_second_order_rigidity_has_asymptotic] using hA
  have hSum :
      Tendsto (fun m => gap m + main m) atTop (nhds (0 + 0)) := by
    exact hGapTendsto.add hMainTendsto
  have hAsymptotic :
      conclusion_boundary_subcritical_perturbation_second_order_rigidity_has_asymptotic countV d M := by
    have hSumZero : Tendsto (fun m => gap m + main m) atTop (nhds 0) := by
      simpa using hSum
    refine Tendsto.congr' ?_ hSumZero
    filter_upwards with m
    have hscale_ne : scale m ≠ 0 := by
      have hscale_pos : 0 < scale m := by
        dsimp [scale, conclusion_boundary_subcritical_perturbation_second_order_rigidity_scale]
        positivity
      linarith
    field_simp [gap, main, hscale_ne]
    ring
  exact ⟨hAsymptotic, hMpos⟩

end Omega.Conclusion
