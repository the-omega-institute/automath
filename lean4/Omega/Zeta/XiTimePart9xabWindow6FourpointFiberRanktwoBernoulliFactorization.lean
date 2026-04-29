import Mathlib.Tactic
import Omega.Zeta.XiTimePart9xabWindow6HiddenFiberAffineBooleanNormalForm

namespace Omega.Zeta

/-- Paper label:
`thm:xi-time-part9xab-window6-fourpoint-fiber-ranktwo-bernoulli-factorization`. -/
theorem paper_xi_time_part9xab_window6_fourpoint_fiber_ranktwo_bernoulli_factorization :
    (∀ base : ℤ,
      xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_hiddenFiber base 2 =
        ({base, base + 34} : Finset ℤ)) ∧
      (∀ base : ℤ,
        xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_hiddenFiber base 3 =
          ({base, base + 21, base + 34} : Finset ℤ)) ∧
      (∀ base : ℤ,
        xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_hiddenFiber base 4 =
          ({base, base + 21, base + 34, base + 55} : Finset ℤ)) ∧
      ((1 + Polynomial.X ^ 21 + Polynomial.X ^ 34 + Polynomial.X ^ 55 : Polynomial ℤ) =
        (1 + Polynomial.X ^ 21) * (1 + Polynomial.X ^ 34)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact paper_xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form.1
  · exact paper_xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form.2.1
  · exact paper_xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form.2.2.1
  · ring_nf

end Omega.Zeta
