import Omega.Conclusion.PartialScreenTraceCutSpaceIdentification
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper-facing screen realizability corollary: once the image of the screen trace is identified
with the cut space, the finite-graph rank formula gives codimension equal to cycle rank, and
surjectivity is equivalent to the screen graph being a forest.
    cor:conclusion-screen-realizability-cycle-space-obstruction -/
theorem paper_conclusion_screen_realizability_cycle_space_obstruction
    (D : PartialScreenTraceData) (u : D.TopChain)
    (vertexCount edgeCount components imageDim : ℕ) (surjective isForest : Prop)
    (hImageDim : imageDim = vertexCount - components)
    (hCompLe : components ≤ vertexCount)
    (hImageLe : imageDim ≤ edgeCount)
    (hSurj : surjective ↔ imageDim = edgeCount)
    (hForest : ((edgeCount : ℤ) - vertexCount + components = 0) ↔ isForest) :
    D.fS u = D.graphCoboundary (D.toVertexLabel u) ∧
      imageDim = vertexCount - components ∧
      ((edgeCount : ℤ) - imageDim = edgeCount - vertexCount + components) ∧
      (surjective ↔ isForest) := by
  refine ⟨paper_conclusion_partial_screen_trace_cut_space_identification D u, hImageDim, ?_, ?_⟩
  · rw [hImageDim]
    omega
  · have hZero : imageDim = edgeCount ↔ ((edgeCount : ℤ) - vertexCount + components = 0) := by
      rw [hImageDim]
      omega
    rw [hSurj, hZero, hForest]

end Omega.Conclusion
