import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part59ac-foldgauge-ratio-one-forty-eighth`. -/
theorem paper_xi_time_part59ac_foldgauge_ratio_one_forty_eighth (φ q0 a1 a2 : ℝ)
    (hφ : φ ^ 2 = φ + 1) (hφpos : 0 < φ) (hq0 : q0 = φ / 2)
    (ha1 : a1 = 1 / (3 * φ)) (ha2 : a2 = -Real.sqrt 5 / 180)
    (hsqrt : Real.sqrt 5 = 2 * φ - 1) :
    (a2 / a1) * (q0 ^ 2 - 1) = (1 : ℝ) / 48 := by
  subst q0
  subst a1
  subst a2
  rw [hsqrt]
  have hφ_ne : φ ≠ 0 := ne_of_gt hφpos
  field_simp [hφ_ne]
  nlinarith

end Omega.Zeta
