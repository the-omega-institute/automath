import Mathlib.Data.Rat.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.GU

/-- The discrete spectrum of the normalized 6-cube walk. -/
def hypercubeSpectrumSix : Finset ℚ :=
  {1, (2 : ℚ) / 3, (1 : ℚ) / 3, 0, -((1 : ℚ) / 3), -((2 : ℚ) / 3), -1}

theorem witness₁_not_mem_hypercubeSpectrumSix :
    (4841 : ℚ) / 10000 ∉ hypercubeSpectrumSix := by
  norm_num [hypercubeSpectrumSix]

theorem witness₂_not_mem_hypercubeSpectrumSix :
    (6031 : ℚ) / 10000 ∉ hypercubeSpectrumSix := by
  norm_num [hypercubeSpectrumSix]

/-- Paper-facing spectral falsifier for the strong-lumpability obstruction. -/
theorem paper_window6_strong_lumpability_spectral_falsifier :
    (4841 : ℚ) / 10000 ∉ hypercubeSpectrumSix ∧
      (6031 : ℚ) / 10000 ∉ hypercubeSpectrumSix := by
  exact ⟨witness₁_not_mem_hypercubeSpectrumSix, witness₂_not_mem_hypercubeSpectrumSix⟩

end Omega.GU
