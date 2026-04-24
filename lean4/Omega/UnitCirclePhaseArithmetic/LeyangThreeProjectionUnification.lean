import Omega.UnitCirclePhaseArithmetic.LeyangLissajousChebyshevResultant
import Omega.UnitCirclePhaseArithmetic.LeyangRationalRoseTorusProjection

namespace Omega.UnitCirclePhaseArithmetic

/-- Paper label: `thm:leyang-three-projection-unification`. -/
theorem paper_leyang_three_projection_unification (xi eta : ℂ) (hxi : Complex.abs xi = 1)
    (heta : Complex.abs eta = 1) (hw0 : ((eta / 2) * (xi + xi⁻¹)) ≠ 0) (a b : ℕ) (t δ : ℝ)
    (hb : 1 ≤ b) (hθ : Real.sin ((a : ℝ) * t + δ) ≠ 0) :
    let w : ℂ := (eta / 2) * (xi + xi⁻¹)
    let x := leyangLissajousX a t δ
    let y := leyangLissajousY b t
    Complex.abs w = Complex.abs (xi + xi⁻¹) / 2 ∧
      -(1 / (4 * Complex.abs w ^ 2 : ℝ)) = -(1 / (Complex.abs (xi + xi⁻¹) ^ 2 : ℝ)) ∧
      ((x ≠ 0 ∧ y ≠ 0) →
        (-(1 / (4 * x ^ 2)) ≤ -(1 / 4) ∧ -(1 / (4 * y ^ 2)) ≤ -(1 / 4))) := by
  dsimp
  rcases paper_leyang_rational_rose_torus_projection xi eta hxi heta hw0 with ⟨hwabs, hwinv⟩
  rcases paper_leyang_lissajous_chebyshev_resultant a b t δ hb hθ with ⟨_, hpunctured⟩
  exact ⟨hwabs, hwinv, hpunctured⟩

end Omega.UnitCirclePhaseArithmetic
