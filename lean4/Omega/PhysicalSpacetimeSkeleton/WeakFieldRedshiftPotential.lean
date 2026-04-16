import Mathlib.Tactic
import Omega.PhysicalSpacetimeSkeleton.AdmissibleGlobalEinsteinEquation
import Omega.PhysicalSpacetimeSkeleton.LocalRedshift

namespace Omega.PhysicalSpacetimeSkeleton

/-- Weak-field lapse written in terms of the redshift potential. -/
noncomputable def weakFieldLapse (φ : ℝ) : ℝ :=
  Real.exp (-φ)

/-- The weak-field `g₀₀` coefficient. -/
noncomputable def weakFieldMetric00 (φ : ℝ) : ℝ :=
  -(weakFieldLapse φ) ^ 2

/-- The Einstein source term appearing after moving `Λ g` to the right-hand side. -/
def weakFieldPoissonSource (D : AdmissibleEinsteinClosure) : ℝ :=
  D.couplingConstant * D.stressEnergy - D.cosmologicalConstant * D.metric

/-- First-order weak-field expansion of `g₀₀` once the lapse is linearized as `1 - φ`. -/
theorem weakFieldMetric00_of_linear_lapse (φ : ℝ) (hLin : weakFieldLapse φ = 1 - φ) :
    weakFieldMetric00 φ = -(1 - 2 * φ + φ ^ 2) := by
  calc
    weakFieldMetric00 φ = -((1 - φ) ^ 2) := by
      rw [weakFieldMetric00, hLin]
    _ = -(1 - 2 * φ + φ ^ 2) := by ring

/-- The admissible Einstein equation rewritten as a Poisson-source identity for the linearized
`00`-component. -/
theorem einsteinTensor_eq_weakFieldPoissonSource
    (D : AdmissibleEinsteinClosure) (hAdm : D.admissible) :
    D.einsteinTensor = weakFieldPoissonSource D := by
  dsimp [weakFieldPoissonSource]
  linarith [paper_physical_spacetime_admissible_global_einstein_equation D hAdm]

/-- Paper-facing weak-field wrapper: the redshift ratio is controlled by the lapse, the lapse
linearizes to the Newtonian potential, and the admissible Einstein equation supplies the source
term.
    cor:physical-spacetime-weak-field-redshift-potential -/
theorem paper_physical_spacetime_weak_field_redshift_potential
    (D : AdmissibleEinsteinClosure) (hAdm : D.admissible)
    {U : Type} (N : U → Real) (A B : U) (deltaT nuA nuB φ : Real)
    (hNA : N A != 0) (hNB : N B != 0) (hT : deltaT != 0)
    (hA : nuA = 1 / (N A * deltaT)) (hB : nuB = 1 / (N B * deltaT))
    (hLin : weakFieldLapse φ = 1 - φ) :
    nuB / nuA = N A / N B ∧
      weakFieldMetric00 φ = -(1 - 2 * φ + φ ^ 2) ∧
      D.einsteinTensor = weakFieldPoissonSource D := by
  refine ⟨paper_physical_spacetime_local_redshift N A B deltaT nuA nuB hNA hNB hT hA hB, ?_, ?_⟩
  · exact weakFieldMetric00_of_linear_lapse φ hLin
  · exact einsteinTensor_eq_weakFieldPoissonSource D hAdm

end Omega.PhysicalSpacetimeSkeleton
