import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-coordinate-bundle-single-face-strict-zero-one-law`. -/
theorem paper_conclusion_coordinate_bundle_single_face_strict_zero_one_law {Face Layer : Type*}
    [DecidableEq Layer] (layerOf : Face → Layer) (hit : Finset Layer)
    (rankBefore rankAfter entropyBefore entropyAfter : Face → ℕ)
    (hRankHit : ∀ e, layerOf e ∈ hit → rankBefore e = rankAfter e)
    (hRankMiss : ∀ e, layerOf e ∉ hit → rankBefore e = rankAfter e + 1)
    (hEntropyHit : ∀ e, layerOf e ∈ hit → entropyBefore e = entropyAfter e)
    (hEntropyMiss : ∀ e, layerOf e ∉ hit → entropyBefore e = entropyAfter e + 1) :
    ∀ e, rankBefore e = rankAfter e + (if layerOf e ∈ hit then 0 else 1) ∧
      entropyBefore e = entropyAfter e + (if layerOf e ∈ hit then 0 else 1) := by
  intro e
  by_cases h : layerOf e ∈ hit
  · simp [h, hRankHit e h, hEntropyHit e h]
  · simp [h, hRankMiss e h, hEntropyMiss e h]

end Omega.Conclusion
