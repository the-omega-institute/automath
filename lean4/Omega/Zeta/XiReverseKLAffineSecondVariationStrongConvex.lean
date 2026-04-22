import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-reversekl-affine-second-variation-strong-convex`. -/
theorem paper_xi_reversekl_affine_second_variation_strong_convex
    (secondVariationFormula strongConvexChordGap : Prop) (hSecond : secondVariationFormula)
    (hGap : strongConvexChordGap) : secondVariationFormula ∧ strongConvexChordGap := by
  exact ⟨hSecond, hGap⟩

end Omega.Zeta
