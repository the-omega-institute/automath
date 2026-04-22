import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Omega.POM.BCDiscreteJacobianStrictification
import Omega.POM.BCDiscreteStokes

namespace Omega.Conclusion

open Omega.POM
open scoped BigOperators

/-- Concrete bilayer data for the strictification package: the measure layer is the two-fiber
strictification problem, while the computational layer records two `1`-cochains on a fixed finite
Beck--Chevalley nerve. -/
structure conclusion_strictification_bilayer_measure_affine_gauge_data where
  a : ℕ
  b : ℕ
  ha : 0 < a
  hb : 0 < b
  complex : BCDiscreteStokesComplex
  baseGauge : BCDiscreteOneCochain complex
  candidateGauge : BCDiscreteOneCochain complex

namespace conclusion_strictification_bilayer_measure_affine_gauge_data

/-- Measure-layer uniqueness is the already formalized uniqueness of the strictified middle lift. -/
def conclusion_strictification_bilayer_measure_affine_gauge_measure_layer_unique
    (D : conclusion_strictification_bilayer_measure_affine_gauge_data) : Prop :=
  ∀ K : Bool → ℝ,
    TwoPointMarkovKernel K →
      liftAlongTwoFiber D.a D.b K = directUniformLift D.a D.b →
        K = strictifiedMiddleLift D.a D.b

/-- A computational correction is a cocycle when its curvature vanishes. -/
def conclusion_strictification_bilayer_measure_affine_gauge_gauge_cocycle
    (D : conclusion_strictification_bilayer_measure_affine_gauge_data)
    (ζ : BCDiscreteOneCochain D.complex) : Prop :=
  bcCurvatureCochain D.complex ζ = 0

/-- Equality of curvature puts all solutions into the affine translate of the cocycle space
through any chosen base solution. -/
def conclusion_strictification_bilayer_measure_affine_gauge_computational_layer_affine_translate
    (D : conclusion_strictification_bilayer_measure_affine_gauge_data) : Prop :=
  bcCurvatureCochain D.complex D.candidateGauge = bcCurvatureCochain D.complex D.baseGauge →
    ∃ ζ : BCDiscreteOneCochain D.complex,
      D.conclusion_strictification_bilayer_measure_affine_gauge_gauge_cocycle ζ ∧
        D.candidateGauge = fun e => D.baseGauge e + ζ e

end conclusion_strictification_bilayer_measure_affine_gauge_data

open conclusion_strictification_bilayer_measure_affine_gauge_data

/-- Paper-facing bilayer strictification statement: the measure layer is rigid, and the
computational layer is an affine translate of the cocycle space. -/
def conclusion_strictification_bilayer_measure_affine_gauge_statement
    (D : conclusion_strictification_bilayer_measure_affine_gauge_data) : Prop :=
  D.conclusion_strictification_bilayer_measure_affine_gauge_measure_layer_unique ∧
    D.conclusion_strictification_bilayer_measure_affine_gauge_computational_layer_affine_translate

lemma conclusion_strictification_bilayer_measure_affine_gauge_bc_coboundary_sub
    (C : BCDiscreteStokesComplex) (κ η : BCDiscreteOneCochain C) :
    bcCoboundary C (fun e => κ e - η e) = fun f => bcCoboundary C κ f - bcCoboundary C η f := by
  funext f
  simp [bcCoboundary, sub_eq_add_neg, Finset.sum_add_distrib, mul_add]

lemma conclusion_strictification_bilayer_measure_affine_gauge_gauge_cocycle_of_equal_curvature
    (D : conclusion_strictification_bilayer_measure_affine_gauge_data)
    (hcurv : bcCurvatureCochain D.complex D.candidateGauge =
      bcCurvatureCochain D.complex D.baseGauge) :
    D.conclusion_strictification_bilayer_measure_affine_gauge_gauge_cocycle
      (fun e => D.candidateGauge e - D.baseGauge e) := by
  funext f
  have hpoint :
      bcCurvatureCochain D.complex D.candidateGauge f =
        bcCurvatureCochain D.complex D.baseGauge f := congrFun hcurv f
  simpa [conclusion_strictification_bilayer_measure_affine_gauge_gauge_cocycle,
    bcCurvatureCochain,
    conclusion_strictification_bilayer_measure_affine_gauge_bc_coboundary_sub] using
    sub_eq_zero.mpr hpoint

/-- Paper label: `thm:conclusion-strictification-bilayer-measure-affine-gauge`. -/
theorem paper_conclusion_strictification_bilayer_measure_affine_gauge
    (D : conclusion_strictification_bilayer_measure_affine_gauge_data) :
    conclusion_strictification_bilayer_measure_affine_gauge_statement D := by
  refine ⟨?_, ?_⟩
  · intro K hK hLift
    exact
      (paper_pom_bc_discrete_jacobian_strictification D.a D.b D.ha D.hb).2.1 K hK hLift
  · intro hcurv
    refine ⟨fun e => D.candidateGauge e - D.baseGauge e, ?_, ?_⟩
    · exact
        conclusion_strictification_bilayer_measure_affine_gauge_gauge_cocycle_of_equal_curvature
          D hcurv
    · funext e
      ring

end Omega.Conclusion
