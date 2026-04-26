import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

namespace Omega.Zeta

open Complex

/-- Paper label: `prop:xi-phi-diskpole-ratio-identity`. -/
theorem paper_xi_phi_diskpole_ratio_identity (Delta : ℝ) (Phi : ℂ → ℂ)
    (hPhi : ∀ z : ℂ,
      Phi z = Complex.exp (-(Delta : ℂ) * star ((1 + z) / (1 - z))))
    (a b : ℂ) (ha : 1 - a ≠ 0) (hb : 1 - b ≠ 0) :
    Phi a / Phi b =
      Complex.exp (-((2 : ℂ) * (Delta : ℂ)) *
        star ((a - b) / ((1 - a) * (1 - b)))) := by
  have hcayley :
      (1 + a) / (1 - a) - (1 + b) / (1 - b) =
        (2 : ℂ) * (a - b) / ((1 - a) * (1 - b)) := by
    field_simp [ha, hb]
    ring
  have harg :
      -(Delta : ℂ) * star ((1 + a) / (1 - a)) -
          (-(Delta : ℂ) * star ((1 + b) / (1 - b))) =
        -((2 : ℂ) * (Delta : ℂ)) * star ((a - b) / ((1 - a) * (1 - b))) := by
    calc
      -(Delta : ℂ) * star ((1 + a) / (1 - a)) -
          (-(Delta : ℂ) * star ((1 + b) / (1 - b)))
          = -(Delta : ℂ) *
              (star ((1 + a) / (1 - a)) - star ((1 + b) / (1 - b))) := by
            ring
      _ = -(Delta : ℂ) *
              star (((1 + a) / (1 - a)) - ((1 + b) / (1 - b))) := by
            simp
      _ = -(Delta : ℂ) *
              star ((2 : ℂ) * (a - b) / ((1 - a) * (1 - b))) := by
            rw [hcayley]
      _ = -((2 : ℂ) * (Delta : ℂ)) *
            star ((a - b) / ((1 - a) * (1 - b))) := by
            simp [div_eq_mul_inv]
            ring
  rw [hPhi a, hPhi b, ← Complex.exp_sub, harg]

end Omega.Zeta
