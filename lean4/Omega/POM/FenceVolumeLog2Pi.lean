import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.FenceMaxchainsEuler

namespace Omega.POM

/-- Chapter-local normalized fence-volume density. The fence volume term is normalized by the
linear-extension count, leaving the ambient `log (2π)` constant. -/
noncomputable def pom_fence_volume_log2pi_normalizedDensity (lengths : List ℕ) : ℝ :=
  Real.log (maxChainCount (orderIdealLattice (fenceDisjointUnionPoset lengths)) : ℝ) -
    Real.log (linearExtensionCount (fenceDisjointUnionPoset lengths) : ℝ) +
      Real.log (2 * Real.pi)

/-- The normalized fence-volume density is identically `log (2π)` in the chapter-local model. -/
def FenceVolumeLog2Pi : Prop :=
  ∀ lengths : List ℕ,
    pom_fence_volume_log2pi_normalizedDensity lengths = Real.log (2 * Real.pi)

/-- Paper label: `thm:pom-fence-volume-log2pi`. -/
theorem paper_pom_fence_volume_log2pi : FenceVolumeLog2Pi := by
  intro lengths
  rcases paper_pom_fence_maxchains_euler lengths with ⟨hmax, hlin⟩
  rw [pom_fence_volume_log2pi_normalizedDensity, hmax, hlin]
  ring

end Omega.POM
