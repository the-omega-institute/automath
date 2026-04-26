import Mathlib.Tactic

namespace Omega.POM

universe u v

/-- Label-prefixed projection/truncation/fold/curvature data on a resolution tower. -/
structure pom_identity_cone_requires_curvature_reduction_tower_data where
  pom_identity_cone_requires_curvature_reduction_state : ℕ → Type u
  pom_identity_cone_requires_curvature_reduction_value : ℕ → Type v
  pom_identity_cone_requires_curvature_reduction_projection :
    ∀ n,
      pom_identity_cone_requires_curvature_reduction_state (n + 1) →
        pom_identity_cone_requires_curvature_reduction_state n
  pom_identity_cone_requires_curvature_reduction_truncation :
    ∀ n,
      pom_identity_cone_requires_curvature_reduction_value (n + 1) →
        pom_identity_cone_requires_curvature_reduction_value n
  pom_identity_cone_requires_curvature_reduction_fold :
    ∀ n,
      pom_identity_cone_requires_curvature_reduction_state n →
        pom_identity_cone_requires_curvature_reduction_value n
  pom_identity_cone_requires_curvature_reduction_K :
    ∀ n,
      pom_identity_cone_requires_curvature_reduction_state (n + 1) →
        pom_identity_cone_requires_curvature_reduction_value n

/-- Levelwise compatibility of the identity cone with projection and truncation. -/
def pom_identity_cone_requires_curvature_reduction_tower_compatible
    (D : pom_identity_cone_requires_curvature_reduction_tower_data) : Prop :=
  ∀ n x,
    D.pom_identity_cone_requires_curvature_reduction_truncation n
        (D.pom_identity_cone_requires_curvature_reduction_fold (n + 1) x) =
      D.pom_identity_cone_requires_curvature_reduction_fold n
        (D.pom_identity_cone_requires_curvature_reduction_projection n x) ∧
      D.pom_identity_cone_requires_curvature_reduction_K n x =
        D.pom_identity_cone_requires_curvature_reduction_fold n
          (D.pom_identity_cone_requires_curvature_reduction_projection n x)

/-- One-step zero-defect curvature reduction at every adjacent level. -/
def pom_identity_cone_requires_curvature_reduction_one_step_zero_defect
    (D : pom_identity_cone_requires_curvature_reduction_tower_data) : Prop :=
  ∀ n x,
    D.pom_identity_cone_requires_curvature_reduction_truncation n
        (D.pom_identity_cone_requires_curvature_reduction_fold (n + 1) x) =
      D.pom_identity_cone_requires_curvature_reduction_K n x ∧
      D.pom_identity_cone_requires_curvature_reduction_K n x =
        D.pom_identity_cone_requires_curvature_reduction_fold n
          (D.pom_identity_cone_requires_curvature_reduction_projection n x)

/-- Concrete conclusion: the identity cone is compatible exactly when every one-step curvature
defect reduces to zero. -/
def pom_identity_cone_requires_curvature_reduction_statement
    (D : pom_identity_cone_requires_curvature_reduction_tower_data) : Prop :=
  pom_identity_cone_requires_curvature_reduction_tower_compatible D ↔
    pom_identity_cone_requires_curvature_reduction_one_step_zero_defect D

/-- Paper label: `prop:pom-identity-cone-requires-curvature-reduction`. -/
theorem paper_pom_identity_cone_requires_curvature_reduction
    (D : pom_identity_cone_requires_curvature_reduction_tower_data) :
    pom_identity_cone_requires_curvature_reduction_statement D := by
  constructor
  · intro h n x
    exact ⟨(h n x).1.trans (h n x).2.symm, (h n x).2⟩
  · intro h n x
    exact ⟨(h n x).1.trans (h n x).2, (h n x).2⟩

end Omega.POM
