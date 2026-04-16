import Mathlib.Tactic

namespace Omega.PhysicalSpacetimeSkeleton

/-- Minimal abstract interface for an admissible second-order covariant gravitational closure.
It packages the action-equivalence to an affine Ricci-scalar term plus divergence and the
normalization data that fixes the affine representative to `R_g - 2Λ`. -/
structure MinimalSecondOrderCovariantClosure where
  gravitationalScalar : ℝ
  ricciScalar : ℝ
  cosmologicalConstant : ℝ
  admissible : Prop
  affineActionEquivalence :
    admissible → ∃ a b divergence : ℝ,
      gravitationalScalar = a * ricciScalar + b + divergence
  normalizeAffinePart :
    admissible →
      ∀ {a b divergence : ℝ},
        gravitationalScalar = a * ricciScalar + b + divergence →
          a = 1 ∧ b = -2 * cosmologicalConstant

/-- Any admissible minimal second-order covariant closure is action-equivalent to an affine Ricci
term plus a divergence. -/
theorem gravitational_scalar_action_equivalent_to_affine_ricci
    (C : MinimalSecondOrderCovariantClosure) (hAdm : C.admissible) :
    ∃ a b divergence : ℝ,
      C.gravitationalScalar = a * C.ricciScalar + b + divergence :=
  C.affineActionEquivalence hAdm

/-- Paper-facing uniqueness wrapper for admissible gravitational scalars: any admissible closure is
action-equivalent to an affine Ricci-scalar term plus divergence, and the normalized affine
representative is exactly `R_g - 2Λ`.
    thm:physical-spacetime-gravitational-scalar-uniqueness -/
theorem paper_physical_spacetime_gravitational_scalar_uniqueness
    (C : MinimalSecondOrderCovariantClosure) (hAdm : C.admissible) :
    ∃ a b divergence : ℝ,
      C.gravitationalScalar = a * C.ricciScalar + b + divergence ∧
      a = 1 ∧
      b = -2 * C.cosmologicalConstant ∧
      a * C.ricciScalar + b = C.ricciScalar - 2 * C.cosmologicalConstant := by
  obtain ⟨a, b, divergence, hAffine⟩ :=
    gravitational_scalar_action_equivalent_to_affine_ricci C hAdm
  obtain ⟨ha, hb⟩ := C.normalizeAffinePart hAdm hAffine
  refine ⟨a, b, divergence, hAffine, ha, hb, ?_⟩
  calc
    a * C.ricciScalar + b = 1 * C.ricciScalar + (-2 * C.cosmologicalConstant) := by
      simp [ha, hb]
    _ = C.ricciScalar - 2 * C.cosmologicalConstant := by
      ring

end Omega.PhysicalSpacetimeSkeleton
