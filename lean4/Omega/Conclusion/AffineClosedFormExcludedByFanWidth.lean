import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Omega.Conclusion.DiscreteFanWidthTentKernelTomography

namespace Omega.Conclusion

noncomputable section

/-- Paper label: `thm:conclusion-affine-closed-form-excluded-by-fan-width`. -/
theorem paper_conclusion_affine_closed_form_excluded_by_fan_width (c d : ℝ) :
    ∀ q : ℤ,
      Omega.Conclusion.conclusion_discrete_fan_width_tent_kernel_tomography_width
        (fun s : ℝ => c * s + d) q = 0 := by
  intro q
  have hderiv : deriv (fun s : ℝ => c * s + d) = fun _ : ℝ => c := by
    funext s
    rw [deriv_add_const, deriv_const_mul_field]
    simp
  simp [conclusion_discrete_fan_width_tent_kernel_tomography_width,
    conclusion_discrete_fan_width_tent_kernel_tomography_smoothSample, secondDeriv, hderiv]

end

end Omega.Conclusion
