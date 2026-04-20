import Mathlib.Tactic

namespace Omega.Conclusion

/-- The common `Ω₄` fiber cardinality appearing in each of the four `σ_geo` blocks. -/
def window6SigmaGeoFiberCardinality : Nat :=
  2 ^ 4

/-- The four fiberwise families `z_u`, `c_u`, `r_u⁺`, `r_u⁻` all carry one copy of `Ω₄`. -/
def window6SigmaGeoBlockDimensions : List Nat :=
  [window6SigmaGeoFiberCardinality, window6SigmaGeoFiberCardinality,
    window6SigmaGeoFiberCardinality, window6SigmaGeoFiberCardinality]

/-- The ambient six-bit cube has `2⁶ = 64` vertices. -/
def window6AmbientCardinality : Nat :=
  2 ^ 6

/-- Arithmetic shadow of the canonical direct-sum decomposition. -/
def window6SigmaGeoHasCanonicalDirectSum : Prop :=
  window6SigmaGeoBlockDimensions.sum = window6AmbientCardinality

/-- Residual `Q₄` degree together with the two distinguished boundary-coordinate shifts. -/
def window6SigmaGeoAdjacencyDiagonal : List Int :=
  [4, 4, 6, 2]

/-- Arithmetic shadow of the block form `A_{Q₄}, A_{Q₄}, A_{Q₄}+2I, A_{Q₄}-2I`. -/
def window6SigmaGeoAdjacencyBlockForm : Prop :=
  window6SigmaGeoAdjacencyDiagonal = [4 + 0, 4 + 0, 4 + 2, 4 - 2]

/-- `σ_geo` acts by `-1` on the chiral block and by `+1` on the other three blocks. -/
def window6SigmaGeoSignPattern : List Int :=
  [-1, 1, 1, 1]

/-- Arithmetic shadow of the fiberwise sign rule. -/
def window6SigmaGeoSignRule : Prop :=
  window6SigmaGeoSignPattern = [-1, 1, 1, 1]

/-- Paper label: `thm:conclusion-window6-sigma-geo-fourblock-normal-form`. -/
theorem paper_conclusion_window6_sigma_geo_fourblock_normal_form :
    window6SigmaGeoHasCanonicalDirectSum ∧
      window6SigmaGeoAdjacencyBlockForm ∧
      window6SigmaGeoSignRule := by
  unfold window6SigmaGeoHasCanonicalDirectSum window6SigmaGeoBlockDimensions
    window6SigmaGeoFiberCardinality window6AmbientCardinality
    window6SigmaGeoAdjacencyBlockForm window6SigmaGeoAdjacencyDiagonal
    window6SigmaGeoSignRule window6SigmaGeoSignPattern
  native_decide

end Omega.Conclusion
