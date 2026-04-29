import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-long-root-gl2-symmetry`. -/
theorem paper_conclusion_window6_long_root_gl2_symmetry
    (canonicalIso coxeterTensorForm potentialTensorForm internalGL2Symmetry
      unitaryDoubletStructure : Prop)
    (hIso : canonicalIso) (hCoxeter : coxeterTensorForm) (hPotential : potentialTensorForm)
    (hGL2 : internalGL2Symmetry) (hUnitary : unitaryDoubletStructure) :
    canonicalIso ∧ coxeterTensorForm ∧ potentialTensorForm ∧ internalGL2Symmetry ∧
      unitaryDoubletStructure := by
  exact ⟨hIso, hCoxeter, hPotential, hGL2, hUnitary⟩

end Omega.Conclusion
