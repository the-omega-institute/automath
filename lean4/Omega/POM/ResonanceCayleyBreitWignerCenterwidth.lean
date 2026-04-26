import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

namespace Omega.POM

theorem paper_pom_resonance_cayley_breitwigner_centerwidth (η θ : ℝ) :
    let a : ℂ := (η : ℂ) * Complex.exp (θ * Complex.I)
    let w : ℂ := (1 + a) / (1 - a)
    w.re = (1 - η ^ 2) / (1 - 2 * η * Real.cos θ + η ^ 2) ∧
      w.im = (2 * η * Real.sin θ) / (1 - 2 * η * Real.cos θ + η ^ 2) := by
  dsimp
  rw [Complex.div_re, Complex.div_im]
  have hre : (((η : ℂ) * Complex.exp (θ * Complex.I)).re) = η * Real.cos θ := by
    simp [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have him : (((η : ℂ) * Complex.exp (θ * Complex.I)).im) = η * Real.sin θ := by
    simp [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have hnorm :
      Complex.normSq (1 - (η : ℂ) * Complex.exp (θ * Complex.I)) =
        1 - 2 * η * Real.cos θ + η ^ 2 := by
    rw [Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im, hre, him]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  constructor
  · have hsq : η ^ 2 * Real.cos θ ^ 2 + η ^ 2 * Real.sin θ ^ 2 = η ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq θ]
    have hnum :
        (1 + η * Real.cos θ) * (1 - η * Real.cos θ) - η ^ 2 * Real.sin θ ^ 2 = 1 - η ^ 2 := by
      nlinarith [hsq]
    simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, hre, him, hnorm,
      div_eq_mul_inv]
    ring_nf
    set x : ℝ := (1 - 2 * η * Real.cos θ + η ^ 2)⁻¹
    have hsqx : (η ^ 2 * Real.cos θ ^ 2 + η ^ 2 * Real.sin θ ^ 2) * x = η ^ 2 * x := by
      exact congrArg (fun t : ℝ => t * x) hsq
    have hx :
        -(η ^ 2 * Real.cos θ ^ 2 * x) - η ^ 2 * x * Real.sin θ ^ 2 + x = -(η ^ 2 * x) + x := by
      nlinarith [hsqx]
    simpa [x, mul_assoc, mul_left_comm, mul_comm] using hx
  · simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, hre, him, hnorm]
    ring

end Omega.POM
