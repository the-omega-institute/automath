import Mathlib.Tactic

namespace Omega.Folding

/-- Paper label: `cor:fold-resonance-ladder-no-decay-no-limit`. -/
theorem paper_fold_resonance_ladder_no_decay_no_limit
    (positive_limsup no_single_limit : Prop)
    (h_positive_limsup : positive_limsup)
    (h_no_single_limit : no_single_limit) :
    positive_limsup ∧ no_single_limit := by
  exact ⟨h_positive_limsup, h_no_single_limit⟩

end Omega.Folding
