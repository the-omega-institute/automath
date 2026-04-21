import Omega.Conclusion.FoldbinGroupoidTracialSimplex
import Omega.EA.Wedderburn

namespace Omega.EA

open Omega.Conclusion.FoldbinGroupoidTracialSimplex

/-- The finite AF stage attached to fold-groupoid resolution `m`, modeled by its Wedderburn block
indexing set. -/
abbrev foldGroupoidAFStage (m : ℕ) := Omega.X m

/-- The holographic trace at stage `m`, given by the escort weights of the block dimensions. -/
noncomputable def foldGroupoidHolographicTrace (m : ℕ) : foldGroupoidAFStage m → ℝ :=
  escortWeight (fun x : foldGroupoidAFStage m => Omega.X.fiberMultiplicity x)

/-- Paper-facing AF-stage and holographic-trace package: the Wedderburn block dimensions give the
finite-dimensional stage, these dimensions grow monotonically with the refinement level, the pushed
forward uniform microstate weights sum to the total word count, and the normalized escort trace is
a simplex-valued trace state. -/
theorem paper_fold_groupoid_af_inductive_limit_holographic_trace
    (m : ℕ) :
    (∑ x : foldGroupoidAFStage m, (Omega.X.fiberMultiplicity x) ^ 2 = Omega.momentSum 2 m) ∧
      Omega.momentSum 2 m ≤ Omega.momentSum 2 (m + 1) ∧
      (∑ x : foldGroupoidAFStage m, Omega.X.fiberMultiplicity x = 2 ^ m) ∧
      foldGroupoidHolographicTrace m ∈ tracialSimplex (ι := foldGroupoidAFStage m) := by
  refine ⟨rfl, Omega.momentSum_two_mono' m, Omega.X.fiberMultiplicity_total m, ?_⟩
  exact escortWeight_mem_tracialSimplex
    (fun x : foldGroupoidAFStage m => Omega.X.fiberMultiplicity x)
    Omega.X.fiberMultiplicity_pos

end Omega.EA
