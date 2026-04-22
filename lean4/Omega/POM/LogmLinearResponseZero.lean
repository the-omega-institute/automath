import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

namespace Omega.POM

lemma pom_logm_linear_response_zero_even_deriv {f : ℝ → ℝ} {f' : ℝ}
    (heven : ∀ θ, f (-θ) = f θ) (hderiv : HasDerivAt f f' 0) :
    f' = 0 := by
  have hcomp : HasDerivAt (fun θ : ℝ => f (-θ)) (-f') 0 := by
    have hnegArg : HasDerivAt (fun θ : ℝ => -θ) (-1) 0 := by
      simpa using (hasDerivAt_neg (0 : ℝ))
    have hderiv_zero : HasDerivAt f f' (-0 : ℝ) := by
      simpa using hderiv
    simpa [Function.comp] using (HasDerivAt.comp (x := (0 : ℝ)) hderiv_zero hnegArg)
  have hfun : (fun θ : ℝ => f (-θ)) = f := by
    funext θ
    simpa using heven θ
  have hneg : HasDerivAt f (-f') 0 := by
    simpa [hfun] using hcomp
  have hEq : f' = -f' := hderiv.unique hneg
  linarith

/-- Paper label: `cor:pom-logm-linear-response-zero`.
Any differentiable even slice has vanishing linear response at the origin, so the multidimensional
statement follows by restricting to an arbitrary one-parameter slice. -/
theorem paper_pom_logm_linear_response_zero {F : ℝ → ℝ → ℝ} {x deriv : ℝ}
    (heven : ∀ θ, F x (-θ) = F x θ)
    (hderiv : HasDerivAt (fun θ : ℝ => F x θ) deriv 0) :
    deriv = 0 := by
  exact pom_logm_linear_response_zero_even_deriv heven hderiv

end Omega.POM
