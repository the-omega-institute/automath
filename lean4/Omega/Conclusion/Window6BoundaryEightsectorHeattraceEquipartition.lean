import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-boundary-eightsector-heattrace-equipartition`. -/
theorem paper_conclusion_window6_boundary_eightsector_heattrace_equipartition
    {Sector A TraceValue : Type} [Fintype Sector]
    (sectorTrace : Sector → A → TraceValue) (baseTrace : A → TraceValue)
    (hcopy : ∀ χ A, sectorTrace χ A = baseTrace A) :
    ∀ χ ψ A, sectorTrace χ A = sectorTrace ψ A := by
  intro χ ψ A
  rw [hcopy χ A, hcopy ψ A]

end Omega.Conclusion
