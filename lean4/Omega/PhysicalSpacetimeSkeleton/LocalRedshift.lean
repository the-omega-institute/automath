import Mathlib.Tactic
import Omega.PhysicalSpacetimeSkeleton.LocalClockPotential

namespace Omega.PhysicalSpacetimeSkeleton

set_option maxHeartbeats 400000 in
/-- Paper-facing local redshift wrapper: with equal coordinate-time intervals, the effective proper
    times scale by the local lapse, so the reciprocal periods satisfy the usual redshift ratio.
    cor:physical-spacetime-local-redshift -/
theorem paper_physical_spacetime_local_redshift {U : Type} (N : U -> Real) (A B : U)
    (deltaT nuA nuB : Real) (hNA : N A != 0) (hNB : N B != 0) (hT : deltaT != 0)
    (hA : nuA = 1 / (N A * deltaT)) (hB : nuB = 1 / (N B * deltaT)) :
    nuB / nuA = N A / N B := by
  have hNA' : N A ≠ 0 := by simpa using hNA
  have hNB' : N B ≠ 0 := by simpa using hNB
  have hT' : deltaT ≠ 0 := by simpa using hT
  have hAT : N A * deltaT ≠ 0 := mul_ne_zero hNA' hT'
  have hBT : N B * deltaT ≠ 0 := mul_ne_zero hNB' hT'
  rw [hA, hB]
  calc
    (1 / (N B * deltaT)) / (1 / (N A * deltaT)) = (N A * deltaT) / (N B * deltaT) := by
      field_simp [hAT, hBT]
    _ = N A / N B := by
      field_simp [hNB', hT']

end Omega.PhysicalSpacetimeSkeleton
