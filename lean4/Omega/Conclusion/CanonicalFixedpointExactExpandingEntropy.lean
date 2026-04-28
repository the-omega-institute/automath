import Mathlib.Tactic
import Omega.Conclusion.HologramFullshiftTopologicalConjugacy

namespace Omega.Conclusion

noncomputable section

/-- Paper label: `cor:conclusion-canonical-fixedpoint-exact-expanding-entropy`. The canonical
fixed-point model carries the full-shift conjugacy package, and its transported entropy is
exactly `log (M + 1)`. -/
theorem paper_conclusion_canonical_fixedpoint_exact_expanding_entropy (D : CanonicalSliceData) :
    CanonicalFixedpointFullshiftConjugacyStatement D ∧
      conclusion_hologram_fullshift_topological_conjugacy_entropy D = Real.log (D.M + 1) := by
  exact ⟨paper_conclusion_canonical_fixedpoint_fullshift_conjugacy D, rfl⟩

end

end Omega.Conclusion
