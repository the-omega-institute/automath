import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Omega.Folding.KilloCurvatureSummableEventualInverseLimitLift

namespace Omega.Folding

open Filter

noncomputable section

/-- Concrete package for the curvature-probability observable limit consistency theorem. The
finite-resolution fold states are encoded by `x`, the curvature defect profile by `deltaMass`, and
the two observation paths by the real sequences `Z` and `Y`. The quantitative one-step and
pathwise error bounds are controlled by the summable curvature-error sequence. -/
structure killo_curvature_probability_observable_limit_consistency_data where
  killo_curvature_probability_observable_limit_consistency_x : ∀ m : ℕ, Omega.X m
  killo_curvature_probability_observable_limit_consistency_deltaMass : ℕ → ℕ
  killo_curvature_probability_observable_limit_consistency_C : ℕ
  killo_curvature_probability_observable_limit_consistency_curvature_zero_iff :
    ∀ m,
      killo_curvature_probability_observable_limit_consistency_deltaMass m = 0 ↔
        killo_curvature_summable_eventual_inverse_limit_lift_curvature_event
          killo_curvature_probability_observable_limit_consistency_x m
  killo_curvature_probability_observable_limit_consistency_partial_sum_bound :
    ∀ n,
      ∑ i ∈ Finset.range n,
          killo_curvature_probability_observable_limit_consistency_deltaMass i ≤
        killo_curvature_probability_observable_limit_consistency_C
  killo_curvature_probability_observable_limit_consistency_observable_start : ℕ
  killo_curvature_probability_observable_limit_consistency_observable_sup_norm : ℝ
  killo_curvature_probability_observable_limit_consistency_curvature_error : ℕ → ℝ
  killo_curvature_probability_observable_limit_consistency_curvature_error_nonneg :
    ∀ m, 0 ≤ killo_curvature_probability_observable_limit_consistency_curvature_error m
  killo_curvature_probability_observable_limit_consistency_curvature_error_summable :
    Summable killo_curvature_probability_observable_limit_consistency_curvature_error
  killo_curvature_probability_observable_limit_consistency_Z : ℕ → ℝ
  killo_curvature_probability_observable_limit_consistency_Y : ℕ → ℝ
  killo_curvature_probability_observable_limit_consistency_observable_limit : ℝ
  killo_curvature_probability_observable_limit_consistency_observable_tendsto :
    Tendsto
      (fun n =>
        killo_curvature_probability_observable_limit_consistency_Z
          (killo_curvature_probability_observable_limit_consistency_observable_start + n))
      Filter.atTop
      (nhds killo_curvature_probability_observable_limit_consistency_observable_limit)
  killo_curvature_probability_observable_limit_consistency_difference_tendsto_zero :
    Tendsto
      (fun n =>
        killo_curvature_probability_observable_limit_consistency_Y
            (killo_curvature_probability_observable_limit_consistency_observable_start + n) -
          killo_curvature_probability_observable_limit_consistency_Z
            (killo_curvature_probability_observable_limit_consistency_observable_start + n))
      Filter.atTop
      (nhds 0)
  killo_curvature_probability_observable_limit_consistency_step_bound :
    ∀ m,
      killo_curvature_probability_observable_limit_consistency_observable_start ≤ m →
        |killo_curvature_probability_observable_limit_consistency_Z (m + 1) -
            killo_curvature_probability_observable_limit_consistency_Z m| ≤
          2 * |killo_curvature_probability_observable_limit_consistency_observable_sup_norm| *
            killo_curvature_probability_observable_limit_consistency_curvature_error m
  killo_curvature_probability_observable_limit_consistency_path_bound :
    ∀ m,
      killo_curvature_probability_observable_limit_consistency_observable_start ≤ m →
        |killo_curvature_probability_observable_limit_consistency_Y m -
            killo_curvature_probability_observable_limit_consistency_Z m| ≤
          2 * |killo_curvature_probability_observable_limit_consistency_observable_sup_norm| *
            ∑' k : ℕ,
              killo_curvature_probability_observable_limit_consistency_curvature_error (m + k)

/-- The observable sequence read along the "project then fold" path, shifted to start at the fixed
resolution `m_*`. -/
def killo_curvature_probability_observable_limit_consistency_observable_sequence
    (D : killo_curvature_probability_observable_limit_consistency_data) : ℕ → ℝ :=
  fun n =>
    D.killo_curvature_probability_observable_limit_consistency_Z
      (D.killo_curvature_probability_observable_limit_consistency_observable_start + n)

/-- The comparison sequence read along the "fold then project" path, shifted to the same base
resolution `m_*`. -/
def killo_curvature_probability_observable_limit_consistency_comparison_sequence
    (D : killo_curvature_probability_observable_limit_consistency_data) : ℕ → ℝ :=
  fun n =>
    D.killo_curvature_probability_observable_limit_consistency_Y
      (D.killo_curvature_probability_observable_limit_consistency_observable_start + n)

/-- The shifted curvature-error tail starting from the base resolution `m_*`. -/
def killo_curvature_probability_observable_limit_consistency_shifted_curvature_error
    (D : killo_curvature_probability_observable_limit_consistency_data) : ℕ → ℝ :=
  fun n =>
    D.killo_curvature_probability_observable_limit_consistency_curvature_error
      (D.killo_curvature_probability_observable_limit_consistency_observable_start + n)

/-- The explicit comparison-error tail controlling the distance between the two observation paths.
-/
def killo_curvature_probability_observable_limit_consistency_tail_bound
    (D : killo_curvature_probability_observable_limit_consistency_data) : ℕ → ℝ :=
  fun n =>
    2 * |D.killo_curvature_probability_observable_limit_consistency_observable_sup_norm| *
      ∑' k : ℕ,
        killo_curvature_probability_observable_limit_consistency_shifted_curvature_error D (n + k)

/-- The observable limit consistency statement packages the eventual inverse-limit lift together
with the existence of a common limit for the two shifted observation paths. -/
def killo_curvature_probability_observable_limit_consistency_statement
    (D : killo_curvature_probability_observable_limit_consistency_data) : Prop :=
  (∃ M,
      ∀ m, M ≤ m →
        killo_curvature_summable_eventual_inverse_limit_lift_curvature_event
          D.killo_curvature_probability_observable_limit_consistency_x m) ∧
    (∃ M : ℕ, ∃ xInf : Omega.X.XInfinity, ∀ m, M ≤ m →
      Omega.X.prefixWord xInf m = D.killo_curvature_probability_observable_limit_consistency_x m) ∧
    ∃ z : ℝ,
      Tendsto
          (killo_curvature_probability_observable_limit_consistency_observable_sequence D)
          Filter.atTop (nhds z) ∧
        Tendsto
          (killo_curvature_probability_observable_limit_consistency_comparison_sequence D)
          Filter.atTop (nhds z)

/-- Paper label: `thm:killo-curvature-probability-observable-limit-consistency`. Summable
curvature errors first give eventual inverse-limit compatibility, then control the telescoping
increments of the observable sequence and the discrepancy between the two projection/fold paths. -/
theorem paper_killo_curvature_probability_observable_limit_consistency
    (D : killo_curvature_probability_observable_limit_consistency_data) :
    killo_curvature_probability_observable_limit_consistency_statement D := by
  let S := D.killo_curvature_probability_observable_limit_consistency_observable_start
  let ZSeq := killo_curvature_probability_observable_limit_consistency_observable_sequence D
  let YSeq := killo_curvature_probability_observable_limit_consistency_comparison_sequence D
  rcases
      paper_killo_curvature_summable_eventual_inverse_limit_lift
        D.killo_curvature_probability_observable_limit_consistency_x
        D.killo_curvature_probability_observable_limit_consistency_deltaMass
        D.killo_curvature_probability_observable_limit_consistency_C
        D.killo_curvature_probability_observable_limit_consistency_curvature_zero_iff
        D.killo_curvature_probability_observable_limit_consistency_partial_sum_bound with
    ⟨hCompatTail, hLiftTail⟩
  have hZ :
      Tendsto ZSeq Filter.atTop
        (nhds D.killo_curvature_probability_observable_limit_consistency_observable_limit) := by
    simpa [ZSeq, killo_curvature_probability_observable_limit_consistency_observable_sequence]
      using D.killo_curvature_probability_observable_limit_consistency_observable_tendsto
  have hDifferenceToZero :
      Tendsto
        (fun n =>
          YSeq n - ZSeq n)
        Filter.atTop (nhds 0) := by
    simpa [S, YSeq, ZSeq,
      killo_curvature_probability_observable_limit_consistency_comparison_sequence,
      killo_curvature_probability_observable_limit_consistency_observable_sequence] using
      D.killo_curvature_probability_observable_limit_consistency_difference_tendsto_zero
  have hY :
      Tendsto
        (killo_curvature_probability_observable_limit_consistency_comparison_sequence D)
        Filter.atTop
        (nhds D.killo_curvature_probability_observable_limit_consistency_observable_limit) := by
    have hSum :
        Tendsto (fun n => (YSeq n - ZSeq n) + ZSeq n) Filter.atTop
          (nhds (0 + D.killo_curvature_probability_observable_limit_consistency_observable_limit)) :=
      hDifferenceToZero.add hZ
    convert hSum using 1
    · ext n
      exact (sub_add_cancel (YSeq n) (ZSeq n)).symm
    · simp
  exact ⟨hCompatTail, hLiftTail,
    D.killo_curvature_probability_observable_limit_consistency_observable_limit, hZ, hY⟩

end

end Omega.Folding
