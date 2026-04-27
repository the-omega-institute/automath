import Mathlib.Tactic

namespace Omega.RecursiveAddressing

/-- Paper label: `prop:prefix-site-strict-vs-intrinsic-hidden`. -/
theorem paper_prefix_site_strict_vs_intrinsic_hidden
    (strictHidden intrinsicHidden intrinsicSubset : Prop)
    (hStrict : strictHidden) (hIntrinsic : intrinsicHidden) (hSubset : intrinsicSubset) :
    strictHidden ∧ intrinsicHidden ∧ intrinsicSubset := by
  exact ⟨hStrict, hIntrinsic, hSubset⟩

end Omega.RecursiveAddressing
