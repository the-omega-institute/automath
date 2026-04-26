import Mathlib
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Zeta.GmFibonacciSubtowerEntrypointCriterion

namespace Omega.Zeta

noncomputable section

open scoped BigOperators

/-- Pisano-style period proxy used for the major-arc criterion. -/
def gm_zeta_criterion_major_arc_period (q : ℕ) : ℕ :=
  gmFibonacciEntrypoint q

/-- Rational-frequency major-arc sum over one verified Pisano-style period. -/
def gm_zeta_criterion_major_arc_frequency_sum (c : ℝ) (q : ℕ) : ℝ :=
  Finset.sum (Finset.range (gm_zeta_criterion_major_arc_period q)) (fun j => c ^ j)

/-- Period-normalized major-arc frequency sum. -/
def gm_zeta_criterion_major_arc_normalized_frequency_sum (c : ℝ) (q : ℕ) : ℝ :=
  gm_zeta_criterion_major_arc_frequency_sum c q / gm_zeta_criterion_major_arc_period q

/-- Paper label: `prop:gm-zeta-criterion-major-arc`.
Under a concrete strict spectral-gap hypothesis `0 ≤ c < 1`, the Fibonacci/Pisano profinite axis
supplies a positive period and the major-arc rational-frequency sum over one period is uniformly
bounded by that period; after normalization, the average major-arc contribution is at most `1`. -/
theorem paper_gm_zeta_criterion_major_arc (q : ℕ) (hq : 0 < q) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) :
    Nonempty (FibProfiniteCompletion ≃+* Zhat) ∧
      0 < gm_zeta_criterion_major_arc_period q ∧
      gm_zeta_criterion_major_arc_frequency_sum c q ≤ gm_zeta_criterion_major_arc_period q ∧
      gm_zeta_criterion_major_arc_normalized_frequency_sum c q ≤ 1 := by
  have hperiod_pos : 0 < gm_zeta_criterion_major_arc_period q := by
    exact gmFibonacciEntrypoint_pos hq
  have hsum_le :
      gm_zeta_criterion_major_arc_frequency_sum c q ≤ gm_zeta_criterion_major_arc_period q := by
    unfold gm_zeta_criterion_major_arc_frequency_sum gm_zeta_criterion_major_arc_period
    calc
      Finset.sum (Finset.range (gmFibonacciEntrypoint q)) (fun j => c ^ j) ≤
          Finset.sum (Finset.range (gmFibonacciEntrypoint q)) (fun _j => (1 : ℝ)) := by
            exact Finset.sum_le_sum (fun j _hj => pow_le_one₀ hc_nonneg hc_lt_one.le)
      _ = gmFibonacciEntrypoint q := by simp
  have hperiod_real_pos : 0 < (gm_zeta_criterion_major_arc_period q : ℝ) := by
    exact_mod_cast hperiod_pos
  have hnormalized_le_one :
      gm_zeta_criterion_major_arc_normalized_frequency_sum c q ≤ 1 := by
    unfold gm_zeta_criterion_major_arc_normalized_frequency_sum
    refine (div_le_iff₀ hperiod_real_pos).2 ?_
    simpa using hsum_le
  exact ⟨⟨paper_gm_fibonacci_profinite_axis⟩, hperiod_pos, hsum_le, hnormalized_le_one⟩

end

end Omega.Zeta
