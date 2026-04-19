import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper wrapper for the localized-kernel inclusion-exclusion package.
    thm:conclusion-localized-kernel-inclusion-exclusion-mobius -/
theorem paper_conclusion_localized_kernel_inclusion_exclusion_mobius
    (binaryProductFormula grothendieckInclusionExclusion : Prop)
    (hBinary : binaryProductFormula)
    (hMobius : binaryProductFormula -> grothendieckInclusionExclusion) :
    binaryProductFormula ∧ grothendieckInclusionExclusion := by
  exact ⟨hBinary, hMobius hBinary⟩

end Omega.Conclusion
