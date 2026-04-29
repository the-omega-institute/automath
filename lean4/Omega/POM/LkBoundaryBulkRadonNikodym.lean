import Mathlib.Tactic
import Omega.POM.LkBoundarySpectralMeasureBeta32

namespace Omega.POM

noncomputable section

/-- Paper label: `cor:pom-Lk-boundary-bulk-radon-nikodym`.
On the open bulk interval `(0, 4)`, the Beta `(3/2, 3/2)` boundary density is the arcsine bulk
density multiplied by the Radon--Nikodym factor `μ (4 - μ) / 2`. -/
theorem paper_pom_lk_boundary_bulk_radon_nikodym {mu : Real} (hmu0 : 0 < mu) (hmu4 : mu < 4) :
    pom_lk_boundary_spectral_measure_beta32_density mu =
      (mu * (4 - mu) / 2) * (1 / (Real.pi * Real.sqrt (mu * (4 - mu)))) := by
  let x : Real := mu * (4 - mu)
  have h4mu_pos : 0 < 4 - mu := by
    linarith
  have hx_pos : 0 < x := by
    dsimp [x]
    exact mul_pos hmu0 h4mu_pos
  have hsqrt_ne : Real.sqrt x ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 hx_pos)
  have hsqrt_sq : Real.sqrt x * Real.sqrt x = x := by
    nlinarith [Real.sq_sqrt (le_of_lt hx_pos)]
  have hsqrt_ne' : Real.sqrt (mu * (4 - mu)) ≠ 0 := by
    simpa [x] using hsqrt_ne
  have hsqrt_sq' : Real.sqrt (mu * (4 - mu)) * Real.sqrt (mu * (4 - mu)) = mu * (4 - mu) := by
    simpa [x] using hsqrt_sq
  unfold pom_lk_boundary_spectral_measure_beta32_density
  calc
    Real.sqrt (mu * (4 - mu)) / (2 * Real.pi)
        = (Real.sqrt (mu * (4 - mu)) * Real.sqrt (mu * (4 - mu))) /
            ((2 * Real.pi) * Real.sqrt (mu * (4 - mu))) := by
            field_simp [hsqrt_ne']
    _ = (mu * (4 - mu)) / ((2 * Real.pi) * Real.sqrt (mu * (4 - mu))) := by
      rw [hsqrt_sq']
    _ = (mu * (4 - mu) / 2) * (1 / (Real.pi * Real.sqrt (mu * (4 - mu)))) := by
      ring_nf

end

end Omega.POM
