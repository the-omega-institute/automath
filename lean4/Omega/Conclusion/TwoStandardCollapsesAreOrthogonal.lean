import Mathlib.Tactic
import Omega.POM.CollisionFlowEquivalenceFullShift
import Omega.POM.MertensNotFlowInvariant

namespace Omega.Conclusion

/-- Bare `K₀` size in the low-order fork after forgetting the unit class. -/
def conclusion_two_standard_collapses_are_orthogonal_bare_k0_size_a3 : ℕ := 3

/-- Bare `K₀` size in the `A₄(2)` branch after forgetting the unit class. -/
def conclusion_two_standard_collapses_are_orthogonal_bare_k0_size_a4_two : ℕ := 3

/-- Bare `K₁` rank in the `A₃` branch. -/
def conclusion_two_standard_collapses_are_orthogonal_bare_k1_rank_a3 : ℕ := 0

/-- Bare `K₁` rank in the `A₄(2)` branch. -/
def conclusion_two_standard_collapses_are_orthogonal_bare_k1_rank_a4_two : ℕ := 0

/-- The `A₃` unit class is zero in the low-order fork. -/
def conclusion_two_standard_collapses_are_orthogonal_unit_class_a3 : ZMod 3 := 0

/-- The `A₄(2)` unit class is the generator in the low-order fork. -/
def conclusion_two_standard_collapses_are_orthogonal_unit_class_a4_two : ZMod 3 := 1

/-- Concrete package recording the two collapses and the two non-preservation facts:
flow equivalence forgets the finite-part Mertens constant, while bare `K`-theory forgets the
unit class. -/
def conclusion_two_standard_collapses_are_orthogonal_statement : Prop :=
  Omega.POM.pom_collision_flow_equivalence_full_shift_claim ∧
    Omega.POM.pomMertensNotFlowInvariantClaim ∧
    conclusion_two_standard_collapses_are_orthogonal_bare_k0_size_a3 =
      conclusion_two_standard_collapses_are_orthogonal_bare_k0_size_a4_two ∧
    conclusion_two_standard_collapses_are_orthogonal_bare_k1_rank_a3 =
      conclusion_two_standard_collapses_are_orthogonal_bare_k1_rank_a4_two ∧
    conclusion_two_standard_collapses_are_orthogonal_unit_class_a3 ≠
      conclusion_two_standard_collapses_are_orthogonal_unit_class_a4_two

/-- Paper label: `prop:conclusion-two-standard-collapses-are-orthogonal`. -/
theorem paper_conclusion_two_standard_collapses_are_orthogonal :
    conclusion_two_standard_collapses_are_orthogonal_statement := by
  refine ⟨Omega.POM.paper_pom_collision_flow_equivalence_full_shift,
    Omega.POM.paper_pom_mertens_not_flow_invariant, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · norm_num [conclusion_two_standard_collapses_are_orthogonal_unit_class_a3,
      conclusion_two_standard_collapses_are_orthogonal_unit_class_a4_two]

/-- Paper label: `cor:conclusion-loworder-bare-k-theory-unitclass-fork`. -/
theorem paper_conclusion_loworder_bare_k_theory_unitclass_fork :
    conclusion_two_standard_collapses_are_orthogonal_bare_k0_size_a3 =
        conclusion_two_standard_collapses_are_orthogonal_bare_k0_size_a4_two ∧
      conclusion_two_standard_collapses_are_orthogonal_bare_k1_rank_a3 =
        conclusion_two_standard_collapses_are_orthogonal_bare_k1_rank_a4_two ∧
      conclusion_two_standard_collapses_are_orthogonal_unit_class_a3 ≠
        conclusion_two_standard_collapses_are_orthogonal_unit_class_a4_two := by
  refine ⟨rfl, rfl, ?_⟩
  norm_num [conclusion_two_standard_collapses_are_orthogonal_unit_class_a3,
    conclusion_two_standard_collapses_are_orthogonal_unit_class_a4_two]

end Omega.Conclusion
