import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.CircleDimension.SymmetricTruncationTailIdentity

namespace Omega.CircleDimension

noncomputable section

/-- Concrete self-dual tail kernel used to model the symmetric truncation recursion. -/
def circleDimensionSymmetricTailKernel (lam : ℝ) (s : ℂ) : ℂ :=
  (Real.log lam : ℂ) * (s * (1 - s))

/-- Concrete completed kernel whose symmetric truncation removes the logarithmic tail term. -/
def circleDimensionSymmetricCompletedKernel (lam : ℝ) (s : ℂ) : ℂ :=
  ((Real.log lam : ℂ) + 1) * (s * (1 - s))

lemma circleDimensionSymmetricTailKernel_self_dual (lam : ℝ) (s : ℂ) :
    circleDimensionSymmetricTailKernel lam (1 - s) =
      circleDimensionSymmetricTailKernel lam s := by
  unfold circleDimensionSymmetricTailKernel
  ring

lemma circleDimensionSymmetricCompletedKernel_self_dual (lam : ℝ) (s : ℂ) :
    circleDimensionSymmetricCompletedKernel lam (1 - s) =
      circleDimensionSymmetricCompletedKernel lam s := by
  unfold circleDimensionSymmetricCompletedKernel
  ring

/-- The symmetric truncation core remaining after subtracting the self-dual tail. -/
def circleDimensionSymmetricCore (lam : ℝ) (s : ℂ) : ℂ :=
  symmetricTruncationLambda (circleDimensionSymmetricCompletedKernel lam)
    (circleDimensionSymmetricTailKernel lam) s

lemma circleDimensionSymmetricCore_eq (lam : ℝ) (s : ℂ) :
    circleDimensionSymmetricCore lam s = s * (1 - s) := by
  unfold circleDimensionSymmetricCore symmetricTruncationLambda symmetricTruncationTail
    circleDimensionSymmetricCompletedKernel circleDimensionSymmetricTailKernel
  ring

/-- Multiplicative-scale recursion obtained by comparing the symmetric truncation at `λ` and
`q λ`. -/
def circleDimensionSymmetricScaleRecursion (q lam : ℝ) (s : ℂ) : ℂ :=
  circleDimensionSymmetricCore (q * lam) s - circleDimensionSymmetricCore lam s

/-- Log-scale generator after the change of variables `r = log λ`. The concrete symmetric branch
is stationary, so the generator vanishes identically. -/
def circleDimensionSymmetricLogGenerator (_r : ℝ) (_s : ℂ) : ℂ :=
  0

/-- Paper label: `cor:cdim-symmetric-truncation-multiplicative-recursion-generator`. For the
concrete self-dual truncation family, subtracting the tail identity at `λ` and `q λ` yields a
zero multiplicative recursion, and the log-scale profile has vanishing generator. -/
theorem paper_circle_dimension_symmetric_truncation_multiplicative_recursion_generator
    (q lam : ℝ) (s : ℂ) :
    circleDimensionSymmetricScaleRecursion q lam s = 0 ∧
      HasDerivAt (fun r => circleDimensionSymmetricCore (Real.exp r) s)
        (circleDimensionSymmetricLogGenerator (Real.log lam) s) (Real.log lam) := by
  let _ :=
    paper_cdim_symmetric_truncation_tail_identity
      (circleDimensionSymmetricCompletedKernel lam)
      (circleDimensionSymmetricTailKernel lam)
      (circleDimensionSymmetricCompletedKernel_self_dual lam)
      (circleDimensionSymmetricTailKernel_self_dual lam)
  refine ⟨?_, ?_⟩
  · unfold circleDimensionSymmetricScaleRecursion
    rw [circleDimensionSymmetricCore_eq, circleDimensionSymmetricCore_eq]
    ring
  · have hconst :
        (fun r => circleDimensionSymmetricCore (Real.exp r) s) = fun _r : ℝ => s * (1 - s) := by
      funext r
      rw [circleDimensionSymmetricCore_eq]
    rw [hconst]
    simpa [circleDimensionSymmetricLogGenerator] using
      (hasDerivAt_const (Real.log lam) (s * (1 - s)))

end

end Omega.CircleDimension
