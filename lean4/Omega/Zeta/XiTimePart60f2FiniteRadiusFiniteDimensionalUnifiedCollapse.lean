import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite-radius package for the part-60f2 unified collapse. The two observation fibers
are represented by actual finite functions; the Blaschke and solenoid coordinates are concrete
node maps, with distinctness recorded as injectivity. -/
structure xi_time_part60f2_finite_radius_finite_dimensional_unified_collapse_data where
  radius : ℕ
  dimension : ℕ
  observationLeft : Fin radius → ℝ
  observationRight : Fin radius → ℝ
  leftConstant : ℝ
  rightConstant : ℝ
  blaschkeNode : Fin radius → ℂ
  solenoidPoint : Fin radius → ℚ
  hradius_le_dimension : radius ≤ dimension
  hobservationLeft_const : ∀ x, observationLeft x = leftConstant
  hobservationRight_const : ∀ x, observationRight x = rightConstant
  hblaschke_distinct : Function.Injective blaschkeNode
  hsolenoid_distinct : Function.Injective solenoidPoint

namespace xi_time_part60f2_finite_radius_finite_dimensional_unified_collapse_data

/-- The finite-dimensional radius budget fits the ambient model dimension. -/
def xi_time_part60f2_finite_radius_finite_dimensional_unified_collapse_radiusFits
    (D : xi_time_part60f2_finite_radius_finite_dimensional_unified_collapse_data) : Prop :=
  D.radius ≤ D.dimension

/-- Both constant-observation fibers collapse to their packaged scalar observations. -/
def xi_time_part60f2_finite_radius_finite_dimensional_unified_collapse_constantFibers
    (D : xi_time_part60f2_finite_radius_finite_dimensional_unified_collapse_data) : Prop :=
  (∀ x, D.observationLeft x = D.leftConstant) ∧
    ∀ x, D.observationRight x = D.rightConstant

/-- The Blaschke and solenoid coordinates separate all finite-radius points. -/
def xi_time_part60f2_finite_radius_finite_dimensional_unified_collapse_distinctCoordinates
    (D : xi_time_part60f2_finite_radius_finite_dimensional_unified_collapse_data) : Prop :=
  Function.Injective D.blaschkeNode ∧ Function.Injective D.solenoidPoint

/-- Unified witness extracted from the finite-radius data. -/
def unifiedCollapseWitness
    (D : xi_time_part60f2_finite_radius_finite_dimensional_unified_collapse_data) : Prop :=
  D.xi_time_part60f2_finite_radius_finite_dimensional_unified_collapse_radiusFits ∧
    D.xi_time_part60f2_finite_radius_finite_dimensional_unified_collapse_constantFibers ∧
      D.xi_time_part60f2_finite_radius_finite_dimensional_unified_collapse_distinctCoordinates

end xi_time_part60f2_finite_radius_finite_dimensional_unified_collapse_data

/-- Paper label: `thm:xi-time-part60f2-finite-radius-finite-dimensional-unified-collapse`. -/
theorem paper_xi_time_part60f2_finite_radius_finite_dimensional_unified_collapse
    (D : xi_time_part60f2_finite_radius_finite_dimensional_unified_collapse_data) :
    D.unifiedCollapseWitness := by
  refine ⟨D.hradius_le_dimension, ?_, ?_⟩
  · exact ⟨D.hobservationLeft_const, D.hobservationRight_const⟩
  · exact ⟨D.hblaschke_distinct, D.hsolenoid_distinct⟩

end Omega.Zeta
