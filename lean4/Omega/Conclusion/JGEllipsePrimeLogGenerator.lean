import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

namespace Omega.Conclusion

theorem paper_conclusion_jg_ellipse_prime_log_generator (u : ℝ) (p : ℕ) (hp : Nat.Prime p) :
    HasDerivAt (fun t => 2 * Real.cosh (u + t * (Real.log p / 2))) (Real.log p * Real.sinh u) 0 ∧
      HasDerivAt (fun t => 2 * Real.sinh (u + t * (Real.log p / 2))) (Real.log p * Real.cosh u) 0 := by
  have hp_pos : 0 < (p : ℝ) := by
    exact_mod_cast hp.pos
  have hinner : HasDerivAt (fun t : ℝ => u + t * (Real.log p / 2)) (Real.log p / 2) 0 := by
    simpa [mul_comm, mul_left_comm, mul_assoc, add_comm] using
      (HasDerivAt.const_add u ((hasDerivAt_id 0).mul_const (Real.log p / 2)))
  constructor
  · have hcosh : HasDerivAt (fun t => Real.cosh (u + t * (Real.log p / 2)))
        (Real.sinh u * (Real.log p / 2)) 0 := by
      simpa using hinner.cosh
    have hscaled : HasDerivAt (fun t => 2 * Real.cosh (u + t * (Real.log p / 2)))
        (2 * (Real.sinh u * (Real.log p / 2))) 0 := by
      simpa using HasDerivAt.const_mul (2 : ℝ) hcosh
    have hcoeff : 2 * (Real.sinh u * (Real.log p / 2)) = Real.log p * Real.sinh u := by
      ring
    simpa [hcoeff] using hscaled
  · have hsinh : HasDerivAt (fun t => Real.sinh (u + t * (Real.log p / 2)))
        (Real.cosh u * (Real.log p / 2)) 0 := by
      simpa using hinner.sinh
    have hscaled : HasDerivAt (fun t => 2 * Real.sinh (u + t * (Real.log p / 2)))
        (2 * (Real.cosh u * (Real.log p / 2))) 0 := by
      simpa using HasDerivAt.const_mul (2 : ℝ) hsinh
    have hcoeff : 2 * (Real.cosh u * (Real.log p / 2)) = Real.log p * Real.cosh u := by
      ring
    simpa [hcoeff] using hscaled

end Omega.Conclusion
