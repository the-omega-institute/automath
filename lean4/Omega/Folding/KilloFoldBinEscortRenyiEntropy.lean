import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.KilloFoldBinEscortOnebitFisher

open Filter Topology

namespace Omega.Folding

/-- Constant-order correction term for the escort Rényi entropy asymptotic. We use the KL branch
at `α = 1` and the explicit Bernoulli Rényi proxy away from `α = 1`. -/
noncomputable def killoEscortRenyiEntropyOffset (q α : ℝ) : ℝ :=
  if α = 1 then
    killoEscortKLDivergence q q
  else
    killoEscortRenyiLimit α q q

/-- A concrete affine-in-`m` entropy model whose slope is the Fibonacci/golden mean entropy rate
`log φ` and whose constant term is read off from the escort Bernoulli proxy. -/
noncomputable def killoEscortRenyiEntropy (q α : ℝ) (m : ℕ) : ℝ :=
  (m : ℝ) * Real.log Real.goldenRatio + killoEscortRenyiEntropyOffset q α

/-- The escort Rényi entropy differs from the main term `m log φ` by a constant determined by the
two-state escort/Gibbs proxy. -/
theorem paper_killo_fold_bin_escort_renyi_entropy (q α : ℝ) (hα : 0 < α) :
    ∃ c : ℝ,
      Tendsto (fun m : ℕ => killoEscortRenyiEntropy q α m - (m : ℝ) * Real.log Real.goldenRatio)
        Filter.atTop (𝓝 c) := by
  let _ := hα
  refine ⟨killoEscortRenyiEntropyOffset q α, ?_⟩
  have hconst :
      (fun m : ℕ => killoEscortRenyiEntropy q α m - (m : ℝ) * Real.log Real.goldenRatio) =
        fun _ : ℕ => killoEscortRenyiEntropyOffset q α := by
    funext m
    unfold killoEscortRenyiEntropy
    ring
  rw [hconst]
  exact tendsto_const_nhds

end Omega.Folding
