import Omega.Conclusion.ZeckendorfEulerWrappedPoissonFourier
import Mathlib.Tactic

set_option linter.unusedVariables false

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-zeckendorf-euler-wrapped-poisson-superexp-approx`. -/
theorem paper_conclusion_zeckendorf_euler_wrapped_poisson_superexp_approx
    (m : Nat) (T : Real) (tvBound fourierBound superexpRate : Prop) (hTV : tvBound)
    (hFourier : tvBound -> fourierBound) (hRate : tvBound -> superexpRate) :
    And tvBound (And fourierBound superexpRate) := by
  exact ⟨hTV, ⟨hFourier hTV, hRate hTV⟩⟩

/-- Concrete data for the finite-resolution Euler semigroup-defect bound. -/
structure conclusion_zeckendorf_euler_approx_semigroup_defect_data where
  conclusion_zeckendorf_euler_approx_semigroup_defect_distance : ℕ → ℕ → ℝ
  conclusion_zeckendorf_euler_approx_semigroup_defect_convolution : ℕ → ℕ → ℕ
  conclusion_zeckendorf_euler_approx_semigroup_defect_eulerKernel : ℝ → ℕ
  conclusion_zeckendorf_euler_approx_semigroup_defect_wrappedPoissonKernel : ℝ → ℕ
  conclusion_zeckendorf_euler_approx_semigroup_defect_s : ℝ
  conclusion_zeckendorf_euler_approx_semigroup_defect_t : ℝ
  conclusion_zeckendorf_euler_approx_semigroup_defect_error_s : ℝ
  conclusion_zeckendorf_euler_approx_semigroup_defect_error_t : ℝ
  conclusion_zeckendorf_euler_approx_semigroup_defect_error_st : ℝ
  conclusion_zeckendorf_euler_approx_semigroup_defect_bound : ℝ
  conclusion_zeckendorf_euler_approx_semigroup_defect_triangle :
    ∀ a b c,
      conclusion_zeckendorf_euler_approx_semigroup_defect_distance a c ≤
        conclusion_zeckendorf_euler_approx_semigroup_defect_distance a b +
          conclusion_zeckendorf_euler_approx_semigroup_defect_distance b c
  conclusion_zeckendorf_euler_approx_semigroup_defect_convolution_tv_contraction :
    conclusion_zeckendorf_euler_approx_semigroup_defect_distance
        (conclusion_zeckendorf_euler_approx_semigroup_defect_convolution
          (conclusion_zeckendorf_euler_approx_semigroup_defect_eulerKernel
            conclusion_zeckendorf_euler_approx_semigroup_defect_s)
          (conclusion_zeckendorf_euler_approx_semigroup_defect_eulerKernel
            conclusion_zeckendorf_euler_approx_semigroup_defect_t))
        (conclusion_zeckendorf_euler_approx_semigroup_defect_convolution
          (conclusion_zeckendorf_euler_approx_semigroup_defect_wrappedPoissonKernel
            conclusion_zeckendorf_euler_approx_semigroup_defect_s)
          (conclusion_zeckendorf_euler_approx_semigroup_defect_wrappedPoissonKernel
            conclusion_zeckendorf_euler_approx_semigroup_defect_t)) ≤
      conclusion_zeckendorf_euler_approx_semigroup_defect_error_s +
        conclusion_zeckendorf_euler_approx_semigroup_defect_error_t
  conclusion_zeckendorf_euler_approx_semigroup_defect_wrapped_poisson_semigroup :
    conclusion_zeckendorf_euler_approx_semigroup_defect_convolution
        (conclusion_zeckendorf_euler_approx_semigroup_defect_wrappedPoissonKernel
          conclusion_zeckendorf_euler_approx_semigroup_defect_s)
        (conclusion_zeckendorf_euler_approx_semigroup_defect_wrappedPoissonKernel
          conclusion_zeckendorf_euler_approx_semigroup_defect_t) =
      conclusion_zeckendorf_euler_approx_semigroup_defect_wrappedPoissonKernel
        (conclusion_zeckendorf_euler_approx_semigroup_defect_s +
          conclusion_zeckendorf_euler_approx_semigroup_defect_t)
  conclusion_zeckendorf_euler_approx_semigroup_defect_st_approx :
    conclusion_zeckendorf_euler_approx_semigroup_defect_distance
        (conclusion_zeckendorf_euler_approx_semigroup_defect_wrappedPoissonKernel
          (conclusion_zeckendorf_euler_approx_semigroup_defect_s +
            conclusion_zeckendorf_euler_approx_semigroup_defect_t))
        (conclusion_zeckendorf_euler_approx_semigroup_defect_eulerKernel
          (conclusion_zeckendorf_euler_approx_semigroup_defect_s +
            conclusion_zeckendorf_euler_approx_semigroup_defect_t)) ≤
      conclusion_zeckendorf_euler_approx_semigroup_defect_error_st
  conclusion_zeckendorf_euler_approx_semigroup_defect_bound_eq :
    conclusion_zeckendorf_euler_approx_semigroup_defect_bound =
      conclusion_zeckendorf_euler_approx_semigroup_defect_error_s +
        conclusion_zeckendorf_euler_approx_semigroup_defect_error_t +
          conclusion_zeckendorf_euler_approx_semigroup_defect_error_st

namespace conclusion_zeckendorf_euler_approx_semigroup_defect_data

/-- The triangle-inequality semigroup-defect estimate. -/
def conclusion_zeckendorf_euler_approx_semigroup_defect_semigroup_defect_bound
    (D : conclusion_zeckendorf_euler_approx_semigroup_defect_data) : Prop :=
  D.conclusion_zeckendorf_euler_approx_semigroup_defect_distance
      (D.conclusion_zeckendorf_euler_approx_semigroup_defect_convolution
        (D.conclusion_zeckendorf_euler_approx_semigroup_defect_eulerKernel
          D.conclusion_zeckendorf_euler_approx_semigroup_defect_s)
        (D.conclusion_zeckendorf_euler_approx_semigroup_defect_eulerKernel
          D.conclusion_zeckendorf_euler_approx_semigroup_defect_t))
      (D.conclusion_zeckendorf_euler_approx_semigroup_defect_eulerKernel
        (D.conclusion_zeckendorf_euler_approx_semigroup_defect_s +
          D.conclusion_zeckendorf_euler_approx_semigroup_defect_t)) ≤
    D.conclusion_zeckendorf_euler_approx_semigroup_defect_bound

end conclusion_zeckendorf_euler_approx_semigroup_defect_data

open conclusion_zeckendorf_euler_approx_semigroup_defect_data

/-- Paper label: `cor:conclusion-zeckendorf-euler-approx-semigroup-defect`. -/
theorem paper_conclusion_zeckendorf_euler_approx_semigroup_defect
    (D : conclusion_zeckendorf_euler_approx_semigroup_defect_data) :
    D.conclusion_zeckendorf_euler_approx_semigroup_defect_semigroup_defect_bound := by
  let convEuler :=
    D.conclusion_zeckendorf_euler_approx_semigroup_defect_convolution
      (D.conclusion_zeckendorf_euler_approx_semigroup_defect_eulerKernel
        D.conclusion_zeckendorf_euler_approx_semigroup_defect_s)
      (D.conclusion_zeckendorf_euler_approx_semigroup_defect_eulerKernel
        D.conclusion_zeckendorf_euler_approx_semigroup_defect_t)
  let convPoisson :=
    D.conclusion_zeckendorf_euler_approx_semigroup_defect_convolution
      (D.conclusion_zeckendorf_euler_approx_semigroup_defect_wrappedPoissonKernel
        D.conclusion_zeckendorf_euler_approx_semigroup_defect_s)
      (D.conclusion_zeckendorf_euler_approx_semigroup_defect_wrappedPoissonKernel
        D.conclusion_zeckendorf_euler_approx_semigroup_defect_t)
  let eulerST :=
    D.conclusion_zeckendorf_euler_approx_semigroup_defect_eulerKernel
      (D.conclusion_zeckendorf_euler_approx_semigroup_defect_s +
        D.conclusion_zeckendorf_euler_approx_semigroup_defect_t)
  have hcontract :
      D.conclusion_zeckendorf_euler_approx_semigroup_defect_distance convEuler convPoisson ≤
        D.conclusion_zeckendorf_euler_approx_semigroup_defect_error_s +
          D.conclusion_zeckendorf_euler_approx_semigroup_defect_error_t := by
    have hpack :=
      paper_conclusion_zeckendorf_euler_wrapped_poisson_superexp_approx 0 0
        (D.conclusion_zeckendorf_euler_approx_semigroup_defect_distance convEuler convPoisson ≤
          D.conclusion_zeckendorf_euler_approx_semigroup_defect_error_s +
            D.conclusion_zeckendorf_euler_approx_semigroup_defect_error_t)
        True True
        (by
          simpa [convEuler, convPoisson] using
            D.conclusion_zeckendorf_euler_approx_semigroup_defect_convolution_tv_contraction)
        (fun _ => trivial) (fun _ => trivial)
    exact hpack.1
  have htail :
      D.conclusion_zeckendorf_euler_approx_semigroup_defect_distance convPoisson eulerST ≤
        D.conclusion_zeckendorf_euler_approx_semigroup_defect_error_st := by
    simpa [convPoisson, eulerST,
      D.conclusion_zeckendorf_euler_approx_semigroup_defect_wrapped_poisson_semigroup] using
      D.conclusion_zeckendorf_euler_approx_semigroup_defect_st_approx
  have htri :
      D.conclusion_zeckendorf_euler_approx_semigroup_defect_distance convEuler eulerST ≤
        D.conclusion_zeckendorf_euler_approx_semigroup_defect_distance convEuler convPoisson +
          D.conclusion_zeckendorf_euler_approx_semigroup_defect_distance convPoisson eulerST :=
    D.conclusion_zeckendorf_euler_approx_semigroup_defect_triangle convEuler convPoisson eulerST
  have hsum :
      D.conclusion_zeckendorf_euler_approx_semigroup_defect_distance convEuler eulerST ≤
        D.conclusion_zeckendorf_euler_approx_semigroup_defect_error_s +
          D.conclusion_zeckendorf_euler_approx_semigroup_defect_error_t +
            D.conclusion_zeckendorf_euler_approx_semigroup_defect_error_st := by
    linarith
  simpa [conclusion_zeckendorf_euler_approx_semigroup_defect_semigroup_defect_bound,
    convEuler, eulerST, D.conclusion_zeckendorf_euler_approx_semigroup_defect_bound_eq] using hsum

end Omega.Conclusion
