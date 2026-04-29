import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete invariant data for
`thm:conclusion-principal-shadow-local-global-functor-boundary`.

The record exposes two finite-depth witness pairs with equal finite invariants but distinct hosts,
and one inverse-limit invariant that is injective on hosts. -/
structure conclusion_principal_shadow_local_global_functor_boundary_data where
  conclusion_principal_shadow_local_global_functor_boundary_host : Type
  conclusion_principal_shadow_local_global_functor_boundary_finite_depth_invariant :
    conclusion_principal_shadow_local_global_functor_boundary_host → ℕ → ℝ
  conclusion_principal_shadow_local_global_functor_boundary_finite_sample_invariant :
    conclusion_principal_shadow_local_global_functor_boundary_host → ℕ → ℝ
  conclusion_principal_shadow_local_global_functor_boundary_inverse_limit_invariant :
    conclusion_principal_shadow_local_global_functor_boundary_host → ℕ → ℝ
  conclusion_principal_shadow_local_global_functor_boundary_finite_depth_left :
    conclusion_principal_shadow_local_global_functor_boundary_host
  conclusion_principal_shadow_local_global_functor_boundary_finite_depth_right :
    conclusion_principal_shadow_local_global_functor_boundary_host
  conclusion_principal_shadow_local_global_functor_boundary_finite_depth_distinct :
    conclusion_principal_shadow_local_global_functor_boundary_finite_depth_left ≠
      conclusion_principal_shadow_local_global_functor_boundary_finite_depth_right
  conclusion_principal_shadow_local_global_functor_boundary_finite_depth_same :
    conclusion_principal_shadow_local_global_functor_boundary_finite_depth_invariant
        conclusion_principal_shadow_local_global_functor_boundary_finite_depth_left =
      conclusion_principal_shadow_local_global_functor_boundary_finite_depth_invariant
        conclusion_principal_shadow_local_global_functor_boundary_finite_depth_right
  conclusion_principal_shadow_local_global_functor_boundary_finite_sample_left :
    conclusion_principal_shadow_local_global_functor_boundary_host
  conclusion_principal_shadow_local_global_functor_boundary_finite_sample_right :
    conclusion_principal_shadow_local_global_functor_boundary_host
  conclusion_principal_shadow_local_global_functor_boundary_finite_sample_distinct :
    conclusion_principal_shadow_local_global_functor_boundary_finite_sample_left ≠
      conclusion_principal_shadow_local_global_functor_boundary_finite_sample_right
  conclusion_principal_shadow_local_global_functor_boundary_finite_sample_same :
    conclusion_principal_shadow_local_global_functor_boundary_finite_sample_invariant
        conclusion_principal_shadow_local_global_functor_boundary_finite_sample_left =
      conclusion_principal_shadow_local_global_functor_boundary_finite_sample_invariant
        conclusion_principal_shadow_local_global_functor_boundary_finite_sample_right
  conclusion_principal_shadow_local_global_functor_boundary_inverse_limit_injective_hyp :
    Function.Injective
      conclusion_principal_shadow_local_global_functor_boundary_inverse_limit_invariant

namespace conclusion_principal_shadow_local_global_functor_boundary_data

/-- Some distinct hosts share the finite-depth invariant. -/
def conclusion_principal_shadow_local_global_functor_boundary_finite_depth_not_injective
    (D : conclusion_principal_shadow_local_global_functor_boundary_data) : Prop :=
  ∃ K L : D.conclusion_principal_shadow_local_global_functor_boundary_host,
    K ≠ L ∧
      D.conclusion_principal_shadow_local_global_functor_boundary_finite_depth_invariant K =
        D.conclusion_principal_shadow_local_global_functor_boundary_finite_depth_invariant L

/-- Some distinct hosts still share the finite-sample enhanced invariant. -/
def conclusion_principal_shadow_local_global_functor_boundary_finite_sample_not_injective
    (D : conclusion_principal_shadow_local_global_functor_boundary_data) : Prop :=
  ∃ K L : D.conclusion_principal_shadow_local_global_functor_boundary_host,
    K ≠ L ∧
      D.conclusion_principal_shadow_local_global_functor_boundary_finite_sample_invariant K =
        D.conclusion_principal_shadow_local_global_functor_boundary_finite_sample_invariant L

/-- The inverse-limit invariant is injective. -/
def conclusion_principal_shadow_local_global_functor_boundary_inverse_limit_injective
    (D : conclusion_principal_shadow_local_global_functor_boundary_data) : Prop :=
  Function.Injective
    D.conclusion_principal_shadow_local_global_functor_boundary_inverse_limit_invariant

end conclusion_principal_shadow_local_global_functor_boundary_data

/-- Paper label: `thm:conclusion-principal-shadow-local-global-functor-boundary`. -/
theorem paper_conclusion_principal_shadow_local_global_functor_boundary
    (D : conclusion_principal_shadow_local_global_functor_boundary_data) :
    D.conclusion_principal_shadow_local_global_functor_boundary_finite_depth_not_injective ∧
      D.conclusion_principal_shadow_local_global_functor_boundary_finite_sample_not_injective ∧
        D.conclusion_principal_shadow_local_global_functor_boundary_inverse_limit_injective := by
  refine ⟨?_, ?_, D.conclusion_principal_shadow_local_global_functor_boundary_inverse_limit_injective_hyp⟩
  · exact
      ⟨D.conclusion_principal_shadow_local_global_functor_boundary_finite_depth_left,
        D.conclusion_principal_shadow_local_global_functor_boundary_finite_depth_right,
        D.conclusion_principal_shadow_local_global_functor_boundary_finite_depth_distinct,
        D.conclusion_principal_shadow_local_global_functor_boundary_finite_depth_same⟩
  · exact
      ⟨D.conclusion_principal_shadow_local_global_functor_boundary_finite_sample_left,
        D.conclusion_principal_shadow_local_global_functor_boundary_finite_sample_right,
        D.conclusion_principal_shadow_local_global_functor_boundary_finite_sample_distinct,
        D.conclusion_principal_shadow_local_global_functor_boundary_finite_sample_same⟩

end Omega.Conclusion
