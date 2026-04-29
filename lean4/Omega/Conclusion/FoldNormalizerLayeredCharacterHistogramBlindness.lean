import Mathlib.Tactic
import Omega.Conclusion.FoldNormalizerCharactersCompletelyStratified

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-fold-normalizer-layered-character-histogram-blindness`. -/
theorem paper_conclusion_fold_normalizer_layered_character_histogram_blindness
    (layerHistogramMatches characterSystemsAgree parityAuditBlind : Prop)
    (hchars : layerHistogramMatches → characterSystemsAgree)
    (hblind : characterSystemsAgree → parityAuditBlind)
    (h : layerHistogramMatches) :
    characterSystemsAgree ∧ parityAuditBlind := by
  have hsystems : characterSystemsAgree := hchars h
  exact ⟨hsystems, hblind hsystems⟩

end Omega.Conclusion
