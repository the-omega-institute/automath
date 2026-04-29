import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Omega.POM.HalfExponentNeedsExpMomentOrder

open scoped BigOperators

namespace Omega.POM

noncomputable section

/-- Concrete folded finite-state package for the unknot average square-root observable. -/
structure pom_unknot_average_moment_inaccessibility_data where
  State : Type
  instFintype : Fintype State
  instDecidableEq : DecidableEq State
  m : ℕ
  d : State → ℝ
  w : State → ℝ
  Q : ℕ → ℕ
  uniformlyConsistent : Prop
  d_nonneg : ∀ x : State, 0 ≤ d x
  weight_eq : ∀ x : State, w x = d x / (2 : ℝ) ^ m
  subexp_obstructs :
    (∀ c > 0, ∀ M : ℕ, ∃ n ≥ M, Real.log (Q n : ℝ) < c * (n : ℝ)) →
      ¬ uniformlyConsistent

attribute [instance] pom_unknot_average_moment_inaccessibility_data.instFintype
attribute [instance] pom_unknot_average_moment_inaccessibility_data.instDecidableEq

namespace pom_unknot_average_moment_inaccessibility_data

/-- The normalized Hellinger half-moment of the folded weights. -/
def normalized_half_moment (C : pom_unknot_average_moment_inaccessibility_data) : ℝ :=
  ∑ x : C.State, Real.sqrt (C.w x)

/-- The uniform average of the square-root fiber observable, in the same normalization. -/
def uniform_sqrt_fiber_average (C : pom_unknot_average_moment_inaccessibility_data) : ℝ :=
  (∑ x : C.State, Real.sqrt (C.d x)) / Real.sqrt ((2 : ℝ) ^ C.m)

/-- The exponential moment-order lower-bound conclusion forced by half-order accessibility. -/
def moment_order_lower_bound (C : pom_unknot_average_moment_inaccessibility_data) : Prop :=
  ∃ c > 0, ∃ M : ℕ, ∀ n ≥ M, c * (n : ℝ) ≤ Real.log (C.Q n : ℝ)

/-- The displayed uniform-average identity together with the finite-moment inaccessibility clause. -/
def statement (C : pom_unknot_average_moment_inaccessibility_data) : Prop :=
  C.normalized_half_moment = C.uniform_sqrt_fiber_average ∧
    (C.uniformlyConsistent → C.moment_order_lower_bound)

lemma sqrt_weight_eq (C : pom_unknot_average_moment_inaccessibility_data) (x : C.State) :
    Real.sqrt (C.w x) = Real.sqrt (C.d x) / Real.sqrt ((2 : ℝ) ^ C.m) := by
  rw [C.weight_eq x]
  rw [Real.sqrt_div (C.d_nonneg x)]

lemma normalized_half_moment_eq_uniform_sqrt_fiber_average
    (C : pom_unknot_average_moment_inaccessibility_data) :
    C.normalized_half_moment = C.uniform_sqrt_fiber_average := by
  simp [normalized_half_moment, uniform_sqrt_fiber_average, sqrt_weight_eq, Finset.sum_div]

end pom_unknot_average_moment_inaccessibility_data

/-- Paper label: `cor:pom-unknot-average-moment-inaccessibility`.
For a finite folded state space with weights `w x = d x / 2^m`, the normalized half-moment is the
uniform square-root fiber average. Uniform consistency then routes through the existing
half-exponent theorem to force exponential moment order. -/
theorem paper_pom_unknot_average_moment_inaccessibility
    (C : pom_unknot_average_moment_inaccessibility_data) : C.statement := by
  refine ⟨?_, ?_⟩
  · exact
      pom_unknot_average_moment_inaccessibility_data.normalized_half_moment_eq_uniform_sqrt_fiber_average
        C
  · exact
      paper_pom_half_exponent_needs_exp_moment_order C.Q C.uniformlyConsistent
        C.subexp_obstructs

end

end Omega.POM
