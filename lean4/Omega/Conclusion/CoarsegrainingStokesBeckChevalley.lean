import Mathlib
import Omega.Conclusion.StokesSteinWeightedGraphMinflow

namespace Omega.Conclusion

open scoped BigOperators

/-- Pull a `0`-cochain on the coarse vertex set back along the coarse-graining map. -/
def coarsePull0Cochain {V W : Type} (phi : V → W) (f : W → ℝ) : V → ℝ :=
  fun v => f (phi v)

/-- Gradient of a `0`-cochain on the fine graph. -/
def fineGradient {V : Type} (g : V → ℝ) : V → V → ℝ :=
  fun u v => g v - g u

/-- Gradient of a `0`-cochain on the coarse graph. -/
def coarseGradient {W : Type} (f : W → ℝ) : W → W → ℝ :=
  fun x y => f y - f x

/-- Chapter-local divergence of a flow on the fine graph. -/
def flowDivergence {V : Type} [Fintype V] (J : V → V → ℝ) : V → ℝ :=
  fun u => ∑ v, (J u v - J v u)

/-- Pair the pulled-back gradient against a fine flow. -/
def coarsePullGradientPairing {V W : Type} [Fintype V] [DecidableEq V] (G : WeightedGraphData V)
    (phi : V → W) (f : W → ℝ) (J : V → V → ℝ) : ℝ :=
  ∑ u, ∑ v, G.edgeWeight u v * fineGradient (coarsePull0Cochain phi f) u v * J u v

/-- The same pairing, but written directly in coarse variables before evaluating on fine edges. -/
def coarsePushGradientPairing {V W : Type} [Fintype V] [DecidableEq V] (G : WeightedGraphData V)
    (phi : V → W) (f : W → ℝ) (J : V → V → ℝ) : ℝ :=
  ∑ u, ∑ v, G.edgeWeight u v * coarseGradient f (phi u) (phi v) * J u v

/-- Pair the pulled-back coarse potential against the fine divergence. -/
def coarsePullDivergencePairing {V W : Type} [Fintype V] [DecidableEq V]
    (_G : WeightedGraphData V) (phi : V → W) (f : W → ℝ) (J : V → V → ℝ) : ℝ :=
  ∑ u, coarsePull0Cochain phi f u * flowDivergence J u

/-- The same divergence pairing written without the explicit pullback helper. -/
def coarsePushDivergencePairing {V W : Type} [Fintype V] [DecidableEq V]
    (_G : WeightedGraphData V) (phi : V → W) (f : W → ℝ) (J : V → V → ℝ) : ℝ :=
  ∑ u, f (phi u) * flowDivergence J u

/-- Paper label: `thm:conclusion-coarsegraining-stokes-beck-chevalley`. -/
theorem paper_conclusion_coarsegraining_stokes_beck_chevalley {V W : Type} [Fintype V]
    [Fintype W] [DecidableEq V] [DecidableEq W] (G : WeightedGraphData V) (phi : V → W)
    (f : W → ℝ) (J : V → V → ℝ) :
    coarsePullGradientPairing G phi f J = coarsePushGradientPairing G phi f J ∧
      coarsePullDivergencePairing G phi f J = coarsePushDivergencePairing G phi f J := by
  constructor <;>
    simp [coarsePullGradientPairing, coarsePushGradientPairing, coarsePullDivergencePairing,
      coarsePushDivergencePairing, fineGradient, coarsePull0Cochain, coarseGradient]

end Omega.Conclusion
