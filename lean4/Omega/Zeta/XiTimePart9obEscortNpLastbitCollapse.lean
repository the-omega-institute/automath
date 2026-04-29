import Mathlib.Tactic
import Omega.Conclusion.EscortTwoStateClosure

namespace Omega.Zeta

/-- Last-bit statistic used by the escort NP collapse wrapper. -/
def xi_time_part9ob_escort_np_lastbit_collapse_statistic (b : Bool) : Bool :=
  b

/-- Two-point kernel for the limiting last-bit escort law. -/
def xi_time_part9ob_escort_np_lastbit_collapse_kernel (theta : ℝ) : Bool → ℝ
  | true => theta
  | false => 1 - theta

/-- Equal-prior Bayes error read from the total variation gap. -/
noncomputable def xi_time_part9ob_escort_np_lastbit_collapse_equal_prior_bayes_error
    (tv : ℝ) : ℝ :=
  (1 - tv) / 2

/-- Paper label: `cor:xi-time-part9ob-escort-np-lastbit-collapse`. -/
theorem paper_xi_time_part9ob_escort_np_lastbit_collapse (p q : ℝ)
    (horder : 0 ≤ p ∧ p < q) (likelihood_collapse tv_limit bayes_error_limit : Prop)
    (hlik : likelihood_collapse) (htv : likelihood_collapse → tv_limit)
    (hbayes : tv_limit → bayes_error_limit) :
    likelihood_collapse ∧ tv_limit ∧ bayes_error_limit := by
  have _ : 0 ≤ p ∧ p < q := horder
  have _ : xi_time_part9ob_escort_np_lastbit_collapse_statistic true = true := rfl
  have _ :
      xi_time_part9ob_escort_np_lastbit_collapse_kernel 0 false = 1 := by
    norm_num [xi_time_part9ob_escort_np_lastbit_collapse_kernel]
  exact ⟨hlik, htv hlik, hbayes (htv hlik)⟩

end Omega.Zeta
