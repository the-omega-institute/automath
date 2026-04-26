import Omega.Conclusion.SquarefreeRTLaminarNesting

namespace Omega.Conclusion

/-- Paper-facing layered normalization wrapper for the squarefree RT laminar minimizer package.
    thm:conclusion-squarefree-cut-layered-normalization -/
theorem paper_conclusion_squarefree_cut_layered_normalization (D : SquarefreeRTLaminarNestingData) :
    D.existsOrderCompatibleSelection ∧ D.canonicalSupports := by
  rcases paper_conclusion_squarefree_rt_laminar_nesting D with ⟨_, hSelection, hSupports⟩
  exact ⟨hSelection, hSupports⟩

end Omega.Conclusion
