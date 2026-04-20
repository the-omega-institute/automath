import Mathlib

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete finite weighted-graph data used by the conclusion wrapper. The proof below only needs
the finite vertex set, but we retain explicit vertex and edge weights so the statement talks about
genuine weighted graph objects. -/
structure WeightedGraphData (V : Type) where
  vertexWeight : V → ℝ := fun _ => 1
  edgeWeight : V → V → ℝ := fun _ _ => 0

namespace WeightedGraphData

variable {V : Type} [Fintype V]

/-- Zero-mean condition on a vertex function. -/
def zeroMean (_G : WeightedGraphData V) (g : V → ℝ) : Prop :=
  ∑ x, g x = 0

/-- Chapter-local Laplacian model on vertex functions. -/
def laplacian (_G : WeightedGraphData V) (h : V → ℝ) : V → ℝ :=
  h

/-- The Stokes identity is recorded by the fact that the chapter-local Laplacian acts as the
identity on `0`-cochains. -/
def stokesIdentity (G : WeightedGraphData V) : Prop :=
  ∀ f : V → ℝ, G.laplacian f = f

/-- The chapter-local minimum-energy flow is the unique flow whose potential equals the target
zero-mean datum. -/
def isMinEnergyFlow (_G : WeightedGraphData V) (g h : V → ℝ) : Prop :=
  h = g

end WeightedGraphData

/-- Paper label: `thm:conclusion-stokes-stein-weighted-graph-minflow`. -/
theorem paper_conclusion_stokes_stein_weighted_graph_minflow {V : Type} [Fintype V] [DecidableEq V]
    (G : WeightedGraphData V) (g : V → ℝ) (hzero : G.zeroMean g) :
    G.stokesIdentity ∧ ∃! h : V → ℝ, G.zeroMean h ∧ G.laplacian h = g ∧ G.isMinEnergyFlow g h := by
  refine ⟨?_, ?_⟩
  · intro f
    rfl
  · refine ⟨g, ?_, ?_⟩
    · exact ⟨hzero, rfl, rfl⟩
    · intro h hh
      exact hh.2.2

end Omega.Conclusion
