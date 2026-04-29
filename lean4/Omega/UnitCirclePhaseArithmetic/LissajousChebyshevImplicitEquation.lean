import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

/-- Paper label: `thm:xi-time-part62d-lissajous-chebyshev-implicit-equation`. -/
theorem paper_xi_time_part62d_lissajous_chebyshev_implicit_equation
    (T : ℕ → ℝ → ℝ) (hT : ∀ k θ, T k (Real.cos θ) = Real.cos ((k : ℝ) * θ))
    (a b : ℕ) (δ t : ℝ) :
    let x := Real.cos ((a : ℝ) * t + δ)
    let y := Real.cos ((b : ℝ) * t)
    T b x ^ 2 - 2 * Real.cos ((b : ℝ) * δ) * T b x * T a y + T a y ^ 2 =
      Real.sin ((b : ℝ) * δ) ^ 2 := by
  dsimp
  set θ : ℝ := ((a * b : ℕ) : ℝ) * t
  set φ : ℝ := (b : ℝ) * δ
  have hb_angle : (b : ℝ) * ((a : ℝ) * t + δ) = θ + φ := by
    dsimp [θ, φ]
    norm_num
    ring
  have ha_angle : (a : ℝ) * ((b : ℝ) * t) = θ := by
    dsimp [θ]
    norm_num
    ring
  have hTb :
      T b (Real.cos ((a : ℝ) * t + δ)) = Real.cos (θ + φ) := by
    calc
      T b (Real.cos ((a : ℝ) * t + δ))
          = Real.cos ((b : ℝ) * ((a : ℝ) * t + δ)) := hT b ((a : ℝ) * t + δ)
      _ = Real.cos (θ + φ) := by rw [hb_angle]
  have hTa : T a (Real.cos ((b : ℝ) * t)) = Real.cos θ := by
    calc
      T a (Real.cos ((b : ℝ) * t)) = Real.cos ((a : ℝ) * ((b : ℝ) * t)) :=
        hT a ((b : ℝ) * t)
      _ = Real.cos θ := by rw [ha_angle]
  rw [hTb, hTa]
  rw [Real.cos_add]
  nlinarith [Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ]

end Omega.UnitCirclePhaseArithmetic
