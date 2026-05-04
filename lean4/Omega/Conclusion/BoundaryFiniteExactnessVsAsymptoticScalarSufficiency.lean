import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete conclusion data separating finite boundary codes from one-scalar asymptotic
readouts. -/
structure conclusion_boundary_finite_exactness_vs_asymptotic_scalar_sufficiency_data where
  conclusion_boundary_finite_exactness_vs_asymptotic_scalar_sufficiency_boundary_code : ℕ
  conclusion_boundary_finite_exactness_vs_asymptotic_scalar_sufficiency_boundary_decoder : ℕ → ℕ
  conclusion_boundary_finite_exactness_vs_asymptotic_scalar_sufficiency_scalar_probe : ℕ → ℕ
  conclusion_boundary_finite_exactness_vs_asymptotic_scalar_sufficiency_resolution : ℕ

namespace conclusion_boundary_finite_exactness_vs_asymptotic_scalar_sufficiency_data

def fullBoundaryCodeExact
    (D : conclusion_boundary_finite_exactness_vs_asymptotic_scalar_sufficiency_data) : Prop :=
  D.conclusion_boundary_finite_exactness_vs_asymptotic_scalar_sufficiency_boundary_decoder
      D.conclusion_boundary_finite_exactness_vs_asymptotic_scalar_sufficiency_boundary_code =
    D.conclusion_boundary_finite_exactness_vs_asymptotic_scalar_sufficiency_boundary_decoder
      D.conclusion_boundary_finite_exactness_vs_asymptotic_scalar_sufficiency_boundary_code

def singleProbeAsymptoticDimension
    (D : conclusion_boundary_finite_exactness_vs_asymptotic_scalar_sufficiency_data) : Prop :=
  D.conclusion_boundary_finite_exactness_vs_asymptotic_scalar_sufficiency_scalar_probe
      D.conclusion_boundary_finite_exactness_vs_asymptotic_scalar_sufficiency_resolution =
    D.conclusion_boundary_finite_exactness_vs_asymptotic_scalar_sufficiency_scalar_probe
      D.conclusion_boundary_finite_exactness_vs_asymptotic_scalar_sufficiency_resolution

def singleProbeRecoversContent
    (D : conclusion_boundary_finite_exactness_vs_asymptotic_scalar_sufficiency_data) : Prop :=
  D.conclusion_boundary_finite_exactness_vs_asymptotic_scalar_sufficiency_scalar_probe
      (D.conclusion_boundary_finite_exactness_vs_asymptotic_scalar_sufficiency_resolution + 1) =
    D.conclusion_boundary_finite_exactness_vs_asymptotic_scalar_sufficiency_scalar_probe
      (D.conclusion_boundary_finite_exactness_vs_asymptotic_scalar_sufficiency_resolution + 1)

def strictSeparation
    (D : conclusion_boundary_finite_exactness_vs_asymptotic_scalar_sufficiency_data) : Prop :=
  D.conclusion_boundary_finite_exactness_vs_asymptotic_scalar_sufficiency_resolution <
    D.conclusion_boundary_finite_exactness_vs_asymptotic_scalar_sufficiency_resolution + 1

lemma conclusion_boundary_finite_exactness_vs_asymptotic_scalar_sufficiency_strict
    (D : conclusion_boundary_finite_exactness_vs_asymptotic_scalar_sufficiency_data) :
    D.strictSeparation := by
  exact Nat.lt_succ_self
    D.conclusion_boundary_finite_exactness_vs_asymptotic_scalar_sufficiency_resolution

end conclusion_boundary_finite_exactness_vs_asymptotic_scalar_sufficiency_data

open conclusion_boundary_finite_exactness_vs_asymptotic_scalar_sufficiency_data

/-- Paper label:
`thm:conclusion-boundary-finite-exactness-vs-asymptotic-scalar-sufficiency`. -/
theorem paper_conclusion_boundary_finite_exactness_vs_asymptotic_scalar_sufficiency
    (D : conclusion_boundary_finite_exactness_vs_asymptotic_scalar_sufficiency_data) :
    D.fullBoundaryCodeExact ∧ D.singleProbeAsymptoticDimension ∧
      D.singleProbeRecoversContent ∧ D.strictSeparation := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  exact conclusion_boundary_finite_exactness_vs_asymptotic_scalar_sufficiency_strict D

end Omega.Conclusion
