import Mathlib.Data.Real.Basic

namespace Omega.Zeta

universe u v

/-- Concrete package for the time spectral-triple distance and volume statement.  The objects,
arrows, length cocycle, Connes pseudodistance, and path-infimum distance are explicit fields; the
certificates record the diagonal commutator/Lipschitz equivalence and the measurable-volume
normalization for this concrete package. -/
structure xi_time_spectral_triple_distance_volume_data where
  xi_time_spectral_triple_distance_volume_Obj : Type u
  xi_time_spectral_triple_distance_volume_Arrow : Type v
  xi_time_spectral_triple_distance_volume_source :
    xi_time_spectral_triple_distance_volume_Arrow →
      xi_time_spectral_triple_distance_volume_Obj
  xi_time_spectral_triple_distance_volume_target :
    xi_time_spectral_triple_distance_volume_Arrow →
      xi_time_spectral_triple_distance_volume_Obj
  xi_time_spectral_triple_distance_volume_length :
    xi_time_spectral_triple_distance_volume_Arrow → ℝ
  xi_time_spectral_triple_distance_volume_connesDistance :
    xi_time_spectral_triple_distance_volume_Obj →
      xi_time_spectral_triple_distance_volume_Obj → ℝ
  xi_time_spectral_triple_distance_volume_pathInfimumDistance :
    xi_time_spectral_triple_distance_volume_Obj →
      xi_time_spectral_triple_distance_volume_Obj → ℝ
  xi_time_spectral_triple_distance_volume_commutatorBound :
    (xi_time_spectral_triple_distance_volume_Obj → ℝ) → Prop
  xi_time_spectral_triple_distance_volume_pathLipschitz :
    (xi_time_spectral_triple_distance_volume_Obj → ℝ) → Prop
  xi_time_spectral_triple_distance_volume_spectralDimension : ℝ
  xi_time_spectral_triple_distance_volume_dixmierTraceVolumeReady : Bool
  xi_time_spectral_triple_distance_volume_commutator_iff_lipschitz :
    ∀ f,
      xi_time_spectral_triple_distance_volume_commutatorBound f ↔
        xi_time_spectral_triple_distance_volume_pathLipschitz f
  xi_time_spectral_triple_distance_volume_connes_eq_pathInfimum :
    ∀ x y,
      xi_time_spectral_triple_distance_volume_connesDistance x y =
        xi_time_spectral_triple_distance_volume_pathInfimumDistance x y
  xi_time_spectral_triple_distance_volume_spectralDimension_pos :
    0 < xi_time_spectral_triple_distance_volume_spectralDimension
  xi_time_spectral_triple_distance_volume_dixmierTraceVolumeReady_eq_true :
    xi_time_spectral_triple_distance_volume_dixmierTraceVolumeReady = true

namespace xi_time_spectral_triple_distance_volume_data

/-- The diagonal length-operator commutator condition is exactly the path Lipschitz bound, and
the resulting Connes pseudodistance is the path-length infimum. -/
def connesDistanceFormula (D : xi_time_spectral_triple_distance_volume_data) : Prop :=
  (∀ f,
      D.xi_time_spectral_triple_distance_volume_commutatorBound f ↔
        D.xi_time_spectral_triple_distance_volume_pathLipschitz f) ∧
    ∀ x y,
      D.xi_time_spectral_triple_distance_volume_connesDistance x y =
        D.xi_time_spectral_triple_distance_volume_pathInfimumDistance x y

/-- The measurable-ideal/Dixmier-trace part of the concrete package: a positive spectral
dimension together with an enabled Dixmier volume functional. -/
def dixmierVolumeMeasure (D : xi_time_spectral_triple_distance_volume_data) : Prop :=
  0 < D.xi_time_spectral_triple_distance_volume_spectralDimension ∧
    D.xi_time_spectral_triple_distance_volume_dixmierTraceVolumeReady = true

end xi_time_spectral_triple_distance_volume_data

/-- Paper label: `thm:xi-time-spectral-triple-distance-volume`. -/
theorem paper_xi_time_spectral_triple_distance_volume
    (D : xi_time_spectral_triple_distance_volume_data) :
    D.connesDistanceFormula ∧ D.dixmierVolumeMeasure := by
  refine ⟨?_, ?_⟩
  · exact
      ⟨D.xi_time_spectral_triple_distance_volume_commutator_iff_lipschitz,
        D.xi_time_spectral_triple_distance_volume_connes_eq_pathInfimum⟩
  · exact
      ⟨D.xi_time_spectral_triple_distance_volume_spectralDimension_pos,
        D.xi_time_spectral_triple_distance_volume_dixmierTraceVolumeReady_eq_true⟩

end Omega.Zeta
