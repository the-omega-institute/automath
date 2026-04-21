import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.LeyangLissajousChebyshevResultant

namespace Omega.UnitCirclePhaseArithmetic

/-- Paper label: `thm:leyang-lissajous-leyang-chebyshev-elimination-special-phases`. -/
theorem paper_leyang_lissajous_leyang_chebyshev_elimination_special_phases (a b : ℕ) (t : ℝ) :
    let tx0 := -(1 / (4 * leyangLissajousX a t 0 ^ 2))
    let tx1 := -(1 / (4 * leyangLissajousX a t (Real.pi / 2) ^ 2))
    let ty := -(1 / (4 * leyangLissajousY b t ^ 2))
    tx0 = -(1 / (2 * (1 + Real.cos (2 * ((a : ℝ) * t))))) ∧
      tx1 = -(1 / (2 * (1 - Real.cos (2 * ((a : ℝ) * t))))) ∧
      ty = -(1 / (2 * (1 + Real.cos (2 * ((b : ℝ) * t))))) := by
  dsimp
  set θa : ℝ := (a : ℝ) * t
  set θb : ℝ := (b : ℝ) * t
  have hcos : 2 * Real.cos θa ^ 2 = 1 + Real.cos (2 * θa) := by
    nlinarith [Real.cos_two_mul θa]
  have hsin : 2 * Real.sin θa ^ 2 = 1 - Real.cos (2 * θa) := by
    nlinarith [Real.cos_two_mul θa, Real.sin_sq_add_cos_sq θa]
  have hcosb : 2 * Real.cos θb ^ 2 = 1 + Real.cos (2 * θb) := by
    nlinarith [Real.cos_two_mul θb]
  constructor
  · calc
      -(1 / (4 * leyangLissajousX a t 0 ^ 2))
          = -(1 / (4 * Real.cos θa ^ 2)) := by simp [leyangLissajousX, θa]
      _ = -(1 / (2 * (2 * Real.cos θa ^ 2))) := by ring
      _ = -(1 / (2 * (1 + Real.cos (2 * θa)))) := by rw [hcos]
      _ = -(1 / (2 * (1 + Real.cos (2 * ((a : ℝ) * t))))) := by simp [θa]
  constructor
  · calc
      -(1 / (4 * leyangLissajousX a t (Real.pi / 2) ^ 2))
          = -(1 / (4 * Real.sin θa ^ 2)) := by
              simp [leyangLissajousX, θa, Real.cos_add_pi_div_two]
      _ = -(1 / (2 * (2 * Real.sin θa ^ 2))) := by ring
      _ = -(1 / (2 * (1 - Real.cos (2 * θa)))) := by rw [hsin]
      _ = -(1 / (2 * (1 - Real.cos (2 * ((a : ℝ) * t))))) := by simp [θa]
  · calc
      -(1 / (4 * leyangLissajousY b t ^ 2))
          = -(1 / (4 * Real.cos θb ^ 2)) := by simp [leyangLissajousY, θb]
      _ = -(1 / (2 * (2 * Real.cos θb ^ 2))) := by ring
      _ = -(1 / (2 * (1 + Real.cos (2 * θb)))) := by rw [hcosb]
      _ = -(1 / (2 * (1 + Real.cos (2 * ((b : ℝ) * t))))) := by simp [θb]

end Omega.UnitCirclePhaseArithmetic
