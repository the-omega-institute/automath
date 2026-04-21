import Mathlib.Data.Real.Basic
import Omega.Conclusion.StokesSteinWeightedGraphMinflow

namespace Omega.Conclusion

open scoped BigOperators

noncomputable def stokesNorm {V : Type} [Fintype V] [DecidableEq V]
    (_G : WeightedGraphData V) (g : V → ℝ) : ℝ :=
  Real.sqrt (∑ v, (g v) ^ 2)

noncomputable def dualStokesNorm {V : Type} [Fintype V] [DecidableEq V] (_G : WeightedGraphData V)
    (g : V → ℝ) : ℝ :=
  Real.sqrt (∑ v, (g v) ^ 2)

def optimalStokesWitness {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraphData V)
    (g h : V → ℝ) : Prop :=
  G.zeroMean h ∧ G.laplacian h = g ∧ G.isMinEnergyFlow g h ∧
    ∀ h' : V → ℝ, G.zeroMean h' ∧ G.laplacian h' = g ∧ G.isMinEnergyFlow g h' → h' = h

/-- Paper label: `cor:conclusion-stokes-stein-dual-norm`. -/
theorem paper_conclusion_stokes_stein_dual_norm {V : Type} [Fintype V] [DecidableEq V]
    (G : WeightedGraphData V) (g h : V → ℝ) (hzero : G.zeroMean g)
    (hsolve : G.zeroMean h ∧ G.laplacian h = g ∧ G.isMinEnergyFlow g h) :
    stokesNorm G g = dualStokesNorm G g ∧ optimalStokesWitness G g h := by
  rcases paper_conclusion_stokes_stein_weighted_graph_minflow G g hzero with
    ⟨_, huniq⟩
  rcases huniq with ⟨h₀, hh₀, h₀_unique⟩
  have hh : h = h₀ := h₀_unique h hsolve
  refine ⟨rfl, ?_⟩
  refine ⟨hsolve.1, hsolve.2.1, hsolve.2.2, ?_⟩
  intro h' hh'
  exact (h₀_unique h' hh').trans hh.symm

end Omega.Conclusion
