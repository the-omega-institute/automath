import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Omega.POM.MinkowskiBudgetBarrier

namespace Omega.POM

/-- The near-1 density main term is the ellipsoid-volume to lattice-covolume ratio, with the
radius specialization rewritten in the paper's `d / 2` real-power form. -/
theorem paper_pom_multi_axis_near1_density
    (d : Nat) (Vd detSigma B lam eps : Real) (hdet : 0 < detSigma) (hB : B ≠ 0)
    (hscale : 0 ≤ 2 * Real.log lam * eps) :
    Omega.POM.pomEllipsoidVolume d Vd detSigma (Real.sqrt (2 * Real.log lam * eps)) /
        Omega.POM.pomLatticeDeterminant d B =
      (B / (2 * Real.pi) ^ d) * (Vd / Real.sqrt detSigma) *
        (2 * Real.log lam * eps) ^ ((d : Real) / 2) := by
  let s : Real := 2 * Real.log lam * eps
  have hsqrt_det : Real.sqrt detSigma ≠ 0 := Real.sqrt_ne_zero'.2 hdet
  have hpi : (2 * Real.pi) ^ d ≠ 0 := by
    exact pow_ne_zero d (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  have hsqrt_pow : (Real.sqrt s) ^ d = s ^ ((d : Real) / 2) := by
    calc
      (Real.sqrt s) ^ d = (s ^ (1 / (2 : Real))) ^ d := by rw [Real.sqrt_eq_rpow]
      _ = s ^ ((1 / (2 : Real)) * (d : Real)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hscale]
      _ = s ^ ((d : Real) / 2) := by
        rw [show (1 / (2 : Real)) * (d : Real) = (d : Real) / 2 by ring]
  have hsqrt_pow' :
      (Real.sqrt (2 * Real.log lam * eps)) ^ d =
        (2 * Real.log lam * eps) ^ ((d : Real) / 2) := by
    simpa [s] using hsqrt_pow
  unfold Omega.POM.pomEllipsoidVolume Omega.POM.pomLatticeDeterminant
  rw [hsqrt_pow']
  field_simp [hB, hpi, hsqrt_det]

end Omega.POM
