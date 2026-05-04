import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-window6-boundary-f8-rational-generated-algebra-blind`. -/
theorem paper_conclusion_window6_boundary_f8_rational_generated_algebra_blind {B G : Type*}
    [Group G] [MulAction G B] (S : Set (B → Complex))
    (hS : ∀ f, f ∈ S → ∀ (g : G) (x : B), f (g • x) = f x) :
    ∀ f, f ∈ Algebra.adjoin Complex S → ∀ (g : G) (x : B), f (g • x) = f x := by
  let invariantSubalgebra : Subalgebra Complex (B → Complex) := {
    carrier := {f | ∀ (g : G) (x : B), f (g • x) = f x}
    zero_mem' := by
      intro g x
      rfl
    one_mem' := by
      intro g x
      rfl
    add_mem' := by
      intro f h hf hk g x
      simp [hf g x, hk g x]
    mul_mem' := by
      intro f h hf hk g x
      simp [hf g x, hk g x]
    algebraMap_mem' := by
      intro c g x
      rfl
  }
  have hle : Algebra.adjoin Complex S ≤ invariantSubalgebra := by
    exact Algebra.adjoin_le hS
  intro f hf g x
  exact hle hf g x

end Omega.Conclusion
