import Mathlib

namespace Omega.Folding

/-- The normalized cumulant sequence obtained after dividing by the dominant
branch-radius term. For this conclusion-layer wrapper the normalization data are
already absorbed into the concrete real sequence `a`. -/
def gaugeAnomalyNormalizedCumulant (_Rθ : ℝ) (a : ℕ → ℝ) : ℕ → ℝ := a

/-- If the normalized cumulants keep returning to values at least `C` and at most
`-C` for arbitrarily large indices, then the raw cumulants have infinitely many
positive and negative values, the normalized sequence does not converge, and no
eventual one-sign tail can occur.
    thm:fold-gauge-anomaly-cumulants-infinite-sign-flips -/
theorem paper_fold_gauge_anomaly_cumulants_infinite_sign_flips
    (κ a : ℕ → ℝ) (Rθ C : ℝ) (σ : ℕ → ℝ)
    (hC : 0 < C)
    (hσ : ∀ n, 0 < σ n)
    (hκ : ∀ n, κ n = σ n * gaugeAnomalyNormalizedCumulant Rθ a n)
    (hpos : ∀ N, ∃ n ≥ N, C ≤ gaugeAnomalyNormalizedCumulant Rθ a n)
    (hneg : ∀ N, ∃ n ≥ N, gaugeAnomalyNormalizedCumulant Rθ a n ≤ -C) :
      (∀ N, ∃ n ≥ N, 0 < κ n) ∧
      (∀ N, ∃ n ≥ N, κ n < 0) ∧
      (¬ ∃ l : ℝ, Filter.Tendsto (gaugeAnomalyNormalizedCumulant Rθ a) Filter.atTop (nhds l)) ∧
      (¬ ∃ N, ∀ n ≥ N, 0 ≤ κ n) ∧
      ¬ ∃ N, ∀ n ≥ N, κ n ≤ 0 := by
  have hposκ : ∀ N, ∃ n ≥ N, 0 < κ n := by
    intro N
    rcases hpos N with ⟨n, hnN, hna⟩
    refine ⟨n, hnN, ?_⟩
    rw [hκ n]
    have hna_pos : 0 < gaugeAnomalyNormalizedCumulant Rθ a n := lt_of_lt_of_le hC hna
    exact mul_pos (hσ n) hna_pos
  have hnegκ : ∀ N, ∃ n ≥ N, κ n < 0 := by
    intro N
    rcases hneg N with ⟨n, hnN, hna⟩
    refine ⟨n, hnN, ?_⟩
    rw [hκ n]
    have hna_neg : gaugeAnomalyNormalizedCumulant Rθ a n < 0 := by
      linarith
    exact mul_neg_of_pos_of_neg (hσ n) hna_neg
  refine ⟨hposκ, hnegκ, ?_, ?_, ?_⟩
  · intro hconv
    rcases hconv with ⟨l, hl⟩
    have hε : 0 < C / 2 := by positivity
    have hmetric :=
      (Metric.tendsto_atTop (u := gaugeAnomalyNormalizedCumulant Rθ a) (a := l)).1 hl
    rcases hmetric (C / 2) hε with ⟨N, hN⟩
    rcases hpos N with ⟨n, hnN, hnpos⟩
    rcases hneg N with ⟨m, hmN, hmneg⟩
    have hsep_nonneg :
        0 ≤ gaugeAnomalyNormalizedCumulant Rθ a n - gaugeAnomalyNormalizedCumulant Rθ a m := by
      linarith
    have hsep :
        2 * C ≤
          |gaugeAnomalyNormalizedCumulant Rθ a n - gaugeAnomalyNormalizedCumulant Rθ a m| := by
      rw [abs_of_nonneg hsep_nonneg]
      linarith
    have htri :
        |gaugeAnomalyNormalizedCumulant Rθ a n - gaugeAnomalyNormalizedCumulant Rθ a m| ≤
          dist (gaugeAnomalyNormalizedCumulant Rθ a n) l +
            dist (gaugeAnomalyNormalizedCumulant Rθ a m) l := by
      calc
        |gaugeAnomalyNormalizedCumulant Rθ a n - gaugeAnomalyNormalizedCumulant Rθ a m|
            = dist (gaugeAnomalyNormalizedCumulant Rθ a n)
                (gaugeAnomalyNormalizedCumulant Rθ a m) := by
                  rw [Real.dist_eq]
        _ ≤ dist (gaugeAnomalyNormalizedCumulant Rθ a n) l +
              dist l (gaugeAnomalyNormalizedCumulant Rθ a m) := dist_triangle _ _ _
        _ = dist (gaugeAnomalyNormalizedCumulant Rθ a n) l +
              dist (gaugeAnomalyNormalizedCumulant Rθ a m) l := by
                rw [dist_comm l]
    have hnclose : dist (gaugeAnomalyNormalizedCumulant Rθ a n) l < C / 2 := hN n hnN
    have hmclose : dist (gaugeAnomalyNormalizedCumulant Rθ a m) l < C / 2 := hN m hmN
    linarith
  · intro htail
    rcases hnegκ htail.choose with ⟨n, hnN, hnneg⟩
    exact not_lt_of_ge (htail.choose_spec n hnN) hnneg
  · intro htail
    rcases hposκ htail.choose with ⟨n, hnN, hnpos⟩
    exact not_lt_of_ge (htail.choose_spec n hnN) hnpos

end Omega.Folding
