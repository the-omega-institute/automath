import Mathlib.Tactic

namespace Omega.POM

/-- Concrete finite zero-temperature selection data: `cost` is the tropical energy,
`bias` is the bounded logarithmic correction, `minCost` is the selected tropical minimum, `gap`
is a uniform positive separation from any non-minimizer, and `biasGap` uniformly bounds the
finite family of bias differences. -/
structure POMZeroTempStableSelectionData (ι : Type _) [Fintype ι] [DecidableEq ι] where
  base : ι
  cost : ι → ℝ
  bias : ι → ℝ
  minCost : ℝ
  gap : ℝ
  biasGap : ℝ
  hbase_min : cost base = minCost
  hmin_le : ∀ i, minCost ≤ cost i
  hgap_pos : 0 < gap
  hgap : ∀ ⦃i : ι⦄, minCost < cost i → gap ≤ cost i - minCost
  hbiasGap_nonneg : 0 ≤ biasGap
  hbiasGap : ∀ i j, |bias i - bias j| ≤ biasGap
  hmin_bias_eq : ∀ ⦃i j : ι⦄, cost i = minCost → cost j = minCost → bias i = bias j

namespace POMZeroTempStableSelectionData

variable {ι : Type _} [Fintype ι] [DecidableEq ι]

/-- The stabilized logarithmic score. -/
noncomputable def score (D : POMZeroTempStableSelectionData ι) (u : ℝ) (i : ι) : ℝ :=
  D.bias i - D.cost i / u

/-- Tropical minimizers. -/
noncomputable def minCostIndices (D : POMZeroTempStableSelectionData ι) : Finset ι :=
  Finset.univ.filter fun i => D.cost i = D.minCost

/-- Maximizers of the stabilized score over the finite candidate set. -/
noncomputable def argmax (D : POMZeroTempStableSelectionData ι) (u : ℝ) : Finset ι :=
  Finset.univ.filter fun i => ∀ j : ι, D.score u j ≤ D.score u i

private lemma score_nonmin_lt_minimizer (D : POMZeroTempStableSelectionData ι) {u : ℝ} {i j : ι}
    (hu : 0 < u) (hu0 : u < D.gap / (D.biasGap + 1)) (hi : D.cost i = D.minCost)
    (hj : D.minCost < D.cost j) : D.score u j < D.score u i := by
  have hden_pos : 0 < D.biasGap + 1 := by
    linarith [D.hbiasGap_nonneg]
  have hgap_le : D.gap ≤ D.cost j - D.minCost := D.hgap hj
  have hcost_div : D.gap / u ≤ (D.cost j - D.minCost) / u := by
    exact div_le_div_of_nonneg_right hgap_le hu.le
  have hmul_lt_gap : u * (D.biasGap + 1) < D.gap := by
    exact (lt_div_iff₀ hden_pos).mp hu0
  have hbiasGap_lt_gap_div : D.biasGap < D.gap / u := by
    apply (lt_div_iff₀ hu).2
    have hbias_mul_lt : D.biasGap * u < u * (D.biasGap + 1) := by
      nlinarith [hu, D.hbiasGap_nonneg]
    linarith
  have hbias_le : D.bias j - D.bias i ≤ D.biasGap := by
    exact (abs_le.mp (D.hbiasGap j i)).2
  have hmain :
      D.bias j - D.bias i < (D.cost j - D.minCost) / u := by
    exact lt_of_le_of_lt hbias_le (lt_of_lt_of_le hbiasGap_lt_gap_div hcost_div)
  have hfrac : D.cost j / u - D.minCost / u = (D.cost j - D.minCost) / u := by
    field_simp [hu.ne']
  have hmain' : D.bias j - D.bias i < D.cost j / u - D.minCost / u := by
    rw [hfrac]
    exact hmain
  have : D.bias j - D.cost j / u < D.bias i - D.minCost / u := by
    linarith
  simpa [score, hi] using this

end POMZeroTempStableSelectionData

open POMZeroTempStableSelectionData

/-- If the tropical cost minimizers share the same logarithmic correction while every
non-minimizer is separated by a uniform positive cost gap, then the finite zero-temperature
argmax stabilizes exactly to the minimizer set.
    cor:pom-zero-temp-stable-selection -/
theorem paper_pom_zero_temp_stable_selection {ι : Type _} [Fintype ι] [DecidableEq ι]
    (D : POMZeroTempStableSelectionData ι) :
    ∃ u0 : ℝ, 0 < u0 ∧ ∀ ⦃u : ℝ⦄, 0 < u → u < u0 → D.argmax u = D.minCostIndices := by
  refine ⟨D.gap / (D.biasGap + 1), ?_, ?_⟩
  · have hden_pos : 0 < D.biasGap + 1 := by
      linarith [D.hbiasGap_nonneg]
    exact div_pos D.hgap_pos hden_pos
  · intro u hu hu0
    ext i
    simp [argmax, minCostIndices]
    constructor
    · intro hi
      by_contra hnot
      have hlt : D.minCost < D.cost i := lt_of_le_of_ne (D.hmin_le i) (by simpa [eq_comm] using hnot)
      have hstrict :
          D.score u i < D.score u D.base :=
        score_nonmin_lt_minimizer D hu hu0 D.hbase_min hlt
      have hbase_le : D.score u D.base ≤ D.score u i := hi D.base
      exact (not_lt_of_ge hbase_le) hstrict
    · intro hi j
      by_cases hj : D.cost j = D.minCost
      · have hbias : D.bias i = D.bias j := D.hmin_bias_eq hi hj
        simp [score, hi, hj, hbias]
      · have hlt : D.minCost < D.cost j := lt_of_le_of_ne (D.hmin_le j) (by simpa [eq_comm] using hj)
        exact le_of_lt (score_nonmin_lt_minimizer D hu hu0 hi hlt)

end Omega.POM
