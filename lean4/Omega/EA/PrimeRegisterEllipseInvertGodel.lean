import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import Omega.EA.JoukowskyEllipse

namespace Omega.EA

/-- Paper-facing inversion formulas for the normalized Joukowsky ellipse parameters.
    thm:prime-register-ellipse-invert-godel -/
theorem paper_prime_register_ellipse_invert_godel (r A B R2 : ℝ) (hr : 1 ≤ r)
    (hA : A = r + r⁻¹) (hB : B = r - r⁻¹) (hR2 : R2 = r^2 + (1 / r)^2) :
    r = (A + B) / 2 ∧ r = Real.sqrt ((R2 + Real.sqrt (R2^2 - 4)) / 2) := by
  have hsum : r = (A + B) / 2 := by
    rw [hA, hB]
    ring
  have hmoment :
      Omega.EA.JoukowskyEllipse.primeRegisterJoukowskyRadialMomentInvert r := by
    exact Omega.EA.JoukowskyEllipse.paper_prime_register_joukowsky_radial_moment_invert r hr
  rcases hmoment with ⟨hmoment_eq, hinvert⟩
  have hR2' : R2 = Omega.EA.JoukowskyEllipse.joukowskySecondRadialMoment r := by
    calc
      R2 = r ^ 2 + (r⁻¹) ^ 2 := by simpa [one_div] using hR2
      _ = Omega.EA.JoukowskyEllipse.joukowskySecondRadialMoment r := by
        simpa using hmoment_eq.symm
  have hsqrt : r = Real.sqrt ((R2 + Real.sqrt (R2^2 - 4)) / 2) := by
    simpa [hR2'] using hinvert
  exact ⟨hsum, hsqrt⟩

end Omega.EA
