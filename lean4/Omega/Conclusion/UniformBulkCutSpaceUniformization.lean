import Omega.Conclusion.PartialScreenTraceCutSpaceIdentification
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Uniform bulk sources push forward uniformly across a finite screen-trace image whenever every
fiber has the same cardinality, so the total domain size is the common fiber size times the image
size.
    thm:conclusion-uniform-bulk-cut-space-uniformization -/
theorem paper_conclusion_uniform_bulk_cut_space_uniformization (D : PartialScreenTraceData)
    [Fintype D.TopChain] [Fintype D.Edge] (fiberCard vertexCount components : ℕ)
    (hFiber : ∀ y : Set.range D.fS, Fintype.card {u : D.TopChain // D.fS u = y.1} = fiberCard)
    (hImage : Fintype.card (Set.range D.fS) = 2 ^ (vertexCount - components)) :
    Fintype.card D.TopChain = fiberCard * 2 ^ (vertexCount - components) := by
  classical
  let e : D.TopChain ≃ Σ y : Set.range D.fS, {u : D.TopChain // D.fS u = y.1} :=
    { toFun := fun u => ⟨⟨D.fS u, ⟨u, rfl⟩⟩, ⟨u, rfl⟩⟩
      invFun := fun s => s.2.1
      left_inv := by
        intro u
        rfl
      right_inv := by
        intro s
        rcases s with ⟨y, u, hu⟩
        cases y with
        | mk val property =>
            simp at hu
            cases hu
            rfl }
  calc
    Fintype.card D.TopChain
        = ∑ y : Set.range D.fS, Fintype.card {u : D.TopChain // D.fS u = y.1} := by
            simpa [e, Fintype.card_sigma] using Fintype.card_congr e
    _ = ∑ _y : Set.range D.fS, fiberCard := by
          simp [hFiber]
    _ = Fintype.card (Set.range D.fS) * fiberCard := by
          simp
    _ = fiberCard * 2 ^ (vertexCount - components) := by
          rw [hImage]
          simp [Nat.mul_comm]

end Omega.Conclusion
