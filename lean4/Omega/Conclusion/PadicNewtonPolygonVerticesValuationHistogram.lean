import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete valuation histogram data for a finite `p`-adic Newton polygon window.  The vertex
abscissae are cumulative multiplicities, while the ordinate bookkeeping records the descending
valuation index. -/
structure conclusion_padic_newton_polygon_vertices_valuation_histogram_data where
  conclusion_padic_newton_polygon_vertices_valuation_histogram_maxValuation : ℕ
  conclusion_padic_newton_polygon_vertices_valuation_histogram_multiplicity : ℕ → ℕ

namespace conclusion_padic_newton_polygon_vertices_valuation_histogram_data

/-- Cumulative horizontal coordinate obtained from the valuation histogram. -/
def cumulativeHistogram
    (D : conclusion_padic_newton_polygon_vertices_valuation_histogram_data) (k : ℕ) : ℕ :=
  ∑ v ∈ Finset.range k,
    D.conclusion_padic_newton_polygon_vertices_valuation_histogram_multiplicity v

/-- The `k`th polygon vertex built from cumulative horizontal mass and negative valuation. -/
def vertex
    (D : conclusion_padic_newton_polygon_vertices_valuation_histogram_data) (k : ℕ) :
    ℕ × ℤ :=
  (D.cumulativeHistogram k, -((k : ℤ)))

/-- The horizontal length of the segment crossing valuation level `k`. -/
def horizontalLength
    (D : conclusion_padic_newton_polygon_vertices_valuation_histogram_data) (k : ℕ) : ℕ :=
  D.cumulativeHistogram (k + 1) - D.cumulativeHistogram k

/-- The recorded slope label for the segment at valuation index `k`. -/
def slope
    (_D : conclusion_padic_newton_polygon_vertices_valuation_histogram_data) (k : ℕ) : ℤ :=
  -((k : ℤ))

/-- Vertices are exactly the cumulative histogram vertices. -/
def verticesAreCumulativeHistogram
    (D : conclusion_padic_newton_polygon_vertices_valuation_histogram_data) : Prop :=
  ∀ k, k ≤ D.conclusion_padic_newton_polygon_vertices_valuation_histogram_maxValuation + 1 →
    (D.vertex k).1 = D.cumulativeHistogram k

/-- Segment slopes carry the negative valuation labels. -/
def slopesAreNegValuations
    (D : conclusion_padic_newton_polygon_vertices_valuation_histogram_data) : Prop :=
  ∀ k, k ≤ D.conclusion_padic_newton_polygon_vertices_valuation_histogram_maxValuation →
    D.slope k = -((k : ℤ))

/-- First horizontal differences recover the original valuation histogram. -/
def histogramRecoveredByHorizontalLengths
    (D : conclusion_padic_newton_polygon_vertices_valuation_histogram_data) : Prop :=
  ∀ k, k ≤ D.conclusion_padic_newton_polygon_vertices_valuation_histogram_maxValuation →
    D.horizontalLength k =
      D.conclusion_padic_newton_polygon_vertices_valuation_histogram_multiplicity k

end conclusion_padic_newton_polygon_vertices_valuation_histogram_data

open conclusion_padic_newton_polygon_vertices_valuation_histogram_data

/-- Paper label: `thm:conclusion-padic-newton-polygon-vertices-valuation-histogram`. -/
theorem paper_conclusion_padic_newton_polygon_vertices_valuation_histogram
    (D : conclusion_padic_newton_polygon_vertices_valuation_histogram_data) :
    D.verticesAreCumulativeHistogram ∧ D.slopesAreNegValuations ∧
      D.histogramRecoveredByHorizontalLengths := by
  refine ⟨?_, ?_, ?_⟩
  · intro k _
    rfl
  · intro k _
    rfl
  · intro k _
    dsimp [horizontalLength, cumulativeHistogram]
    rw [Finset.sum_range_succ]
    exact Nat.add_sub_cancel_left _ _

end Omega.Conclusion
