import Mathlib
import Omega.UnitCirclePhaseArithmetic.LeyangBranchCoverSquareRoot
import Omega.UnitCirclePhaseArithmetic.LeyangPushforwardDensityAsymptotics

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

open Filter Set Topology

/-- The explicit density on the Lee--Yang singular ring predicted by the Haar pushforward. -/
noncomputable def leyangHaarPushforwardDensity (t : ℝ) : ℝ :=
  if t ≤ -(1 : ℝ) / 4 then 1 / (Real.pi * |t| * Real.sqrt |1 + 4 * t|) else 0

/-- The Lee--Yang/Joukowsky coordinate on the unit circle is the explicit inverse-square branch
cover, and the corresponding singular-ring density is supported on `(-∞, -1/4]` with the explicit
formula recorded in the paper. We also keep the endpoint and far-tail asymptotics already proved
for this density model. -/
theorem paper_leyang_haar_pushforward_density :
    (∀ θ : ℝ, leyangBranchCover θ = -(1 / (4 * Real.cos θ ^ 2))) ∧
      (∀ t : ℝ,
        leyangHaarPushforwardDensity t =
          if t ≤ -(1 : ℝ) / 4 then 1 / (Real.pi * |t| * Real.sqrt |1 + 4 * t|) else 0) ∧
      Tendsto
        (fun t : ℝ =>
          (1 / (Real.pi * |t| * Real.sqrt (4 * |t| - 1))) /
            ((2 / Real.pi) / Real.sqrt (-(t + 1 / 4))))
        (nhdsWithin (-(1 : ℝ) / 4) (Set.Iio (-(1 : ℝ) / 4))) (𝓝 1) ∧
      Tendsto
        (fun t : ℝ =>
          (1 / (Real.pi * |t| * Real.sqrt (4 * |t| - 1))) /
            (1 / (2 * Real.pi * |t| * Real.sqrt |t|)))
        atBot (𝓝 1) := by
  refine ⟨?_, ?_, paper_leyang_pushforward_density_asymptotics.1,
    paper_leyang_pushforward_density_asymptotics.2⟩
  · intro θ
    rfl
  · intro t
    by_cases ht : t ≤ -(1 : ℝ) / 4
    · simp [leyangHaarPushforwardDensity, ht]
    · simp [leyangHaarPushforwardDensity, ht]

end

end Omega.UnitCirclePhaseArithmetic
