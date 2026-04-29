import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-poisson-second-order-visible-moduli-one-dimensional`. A
second-order visible Poisson difference that is a scalar multiple of a common kernel lies in the
one-dimensional span of that kernel. -/
theorem paper_conclusion_poisson_second_order_visible_moduli_one_dimensional
    (M0 Var Var' : ℝ) (r : ℝ → ℝ) :
    ∃ a : ℝ, (fun x : ℝ => M0 * (Var - Var') * r x) = fun x : ℝ => a * r x := by
  refine ⟨M0 * (Var - Var'), ?_⟩
  funext x
  ring

end Omega.Conclusion
