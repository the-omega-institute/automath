import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

universe u

noncomputable section

/-- Concrete data for `thm:conclusion-torus-cover-degree-potential-identity`.

The affine inverse branch has determinant `degree^{-1}`; the precision potential is the
negative logarithm of that determinant, and the averaging functional preserves constants. -/
structure conclusion_torus_cover_degree_potential_identity_Data where
  conclusion_torus_cover_degree_potential_identity_point : Type u
  conclusion_torus_cover_degree_potential_identity_coverDegree : ℕ
  conclusion_torus_cover_degree_potential_identity_coverDegree_pos :
    0 < conclusion_torus_cover_degree_potential_identity_coverDegree
  conclusion_torus_cover_degree_potential_identity_inverseDerivativeDeterminant :
    conclusion_torus_cover_degree_potential_identity_point → ℝ
  conclusion_torus_cover_degree_potential_identity_inverseDerivativeDeterminant_identity :
    ∀ x : conclusion_torus_cover_degree_potential_identity_point,
      conclusion_torus_cover_degree_potential_identity_inverseDerivativeDeterminant x =
        (conclusion_torus_cover_degree_potential_identity_coverDegree : ℝ)⁻¹
  conclusion_torus_cover_degree_potential_identity_average :
    (conclusion_torus_cover_degree_potential_identity_point → ℝ) → ℝ
  conclusion_torus_cover_degree_potential_identity_average_congr :
    ∀ f g : conclusion_torus_cover_degree_potential_identity_point → ℝ,
      (∀ x, f x = g x) →
        conclusion_torus_cover_degree_potential_identity_average f =
          conclusion_torus_cover_degree_potential_identity_average g
  conclusion_torus_cover_degree_potential_identity_average_const :
    ∀ c : ℝ,
      conclusion_torus_cover_degree_potential_identity_average (fun _ => c) = c

namespace conclusion_torus_cover_degree_potential_identity_Data

/-- The logarithm of the topological cover degree. -/
def logCoverDegree (D : conclusion_torus_cover_degree_potential_identity_Data) : ℝ :=
  Real.log (D.conclusion_torus_cover_degree_potential_identity_coverDegree : ℝ)

/-- Precision potential obtained from the affine right-inverse derivative determinant. -/
def precisionPotential
    (D : conclusion_torus_cover_degree_potential_identity_Data)
    (x : D.conclusion_torus_cover_degree_potential_identity_point) : ℝ :=
  -Real.log
    (D.conclusion_torus_cover_degree_potential_identity_inverseDerivativeDeterminant x)

/-- Pointwise potential identity. -/
def precisionPotentialEqualsLogDegree
    (D : conclusion_torus_cover_degree_potential_identity_Data) : Prop :=
  ∀ x : D.conclusion_torus_cover_degree_potential_identity_point,
    D.precisionPotential x = D.logCoverDegree

/-- Average precision potential over the torus model. -/
def expectedPrecisionPotential
    (D : conclusion_torus_cover_degree_potential_identity_Data) : ℝ :=
  D.conclusion_torus_cover_degree_potential_identity_average D.precisionPotential

/-- The expected potential is the logarithm of the cover degree. -/
def expectedPrecisionPotentialEqualsLogDegree
    (D : conclusion_torus_cover_degree_potential_identity_Data) : Prop :=
  D.expectedPrecisionPotential = D.logCoverDegree

end conclusion_torus_cover_degree_potential_identity_Data

open conclusion_torus_cover_degree_potential_identity_Data

/-- Paper label: `thm:conclusion-torus-cover-degree-potential-identity`. -/
theorem paper_conclusion_torus_cover_degree_potential_identity
    (D : conclusion_torus_cover_degree_potential_identity_Data) :
    D.precisionPotentialEqualsLogDegree ∧ D.expectedPrecisionPotentialEqualsLogDegree := by
  have hpoint : D.precisionPotentialEqualsLogDegree := by
    intro x
    simp [precisionPotential, logCoverDegree,
      D.conclusion_torus_cover_degree_potential_identity_inverseDerivativeDeterminant_identity x,
      Real.log_inv]
  refine ⟨hpoint, ?_⟩
  unfold expectedPrecisionPotentialEqualsLogDegree expectedPrecisionPotential
  calc
    D.conclusion_torus_cover_degree_potential_identity_average D.precisionPotential =
        D.conclusion_torus_cover_degree_potential_identity_average
          (fun _ : D.conclusion_torus_cover_degree_potential_identity_point => D.logCoverDegree) :=
      D.conclusion_torus_cover_degree_potential_identity_average_congr _ _ hpoint
    _ = D.logCoverDegree :=
      D.conclusion_torus_cover_degree_potential_identity_average_const D.logCoverDegree

end

end Omega.Conclusion
