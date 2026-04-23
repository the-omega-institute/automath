import Mathlib.Tactic
import Omega.Zeta.XiSingularRingEllipseWallcrossingAtomicMeasure

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete finite jump data for realizing the ellipse wallcrossing staircase. -/
structure xi_ellipse_wallcrossing_realize_finite_jump_data_data where
  jumpRadii : Finset ℝ
  jumpWeight : ℝ → ℤ
  t : ℝ
  ellipseAverage : ℤ
  jumpRadii_gt_one : ∀ ⦃a : ℝ⦄, a ∈ jumpRadii → 1 < a
  ellipseAverage_eq :
    ellipseAverage =
      Finset.sum jumpRadii
        (fun a => ((-(jumpWeight a) : ℤ) + if a < t then jumpWeight a else 0))

local notation "XiEllipseWallcrossingRealizeFiniteJumpData" =>
  xi_ellipse_wallcrossing_realize_finite_jump_data_data

/-- The always-inside reciprocal poles contribute the negative total jump weight. -/
noncomputable def xi_ellipse_wallcrossing_realize_finite_jump_data_reciprocalPoleSum
    (D : xi_ellipse_wallcrossing_realize_finite_jump_data_data) : ℤ :=
  Finset.sum D.jumpRadii D.jumpWeight

/-- Threshold-crossing poles contribute exactly the filtered jump sum. -/
noncomputable def xi_ellipse_wallcrossing_realize_finite_jump_data_thresholdCrossingSum
    (D : xi_ellipse_wallcrossing_realize_finite_jump_data_data) : ℤ :=
  Finset.sum (D.jumpRadii.filter fun a => a < D.t) D.jumpWeight

/-- The realized ellipse average is the sum of reciprocal-pole and threshold-crossing
contributions. -/
noncomputable def xi_ellipse_wallcrossing_realize_finite_jump_data_realizedEllipseAverage
    (D : xi_ellipse_wallcrossing_realize_finite_jump_data_data) : ℤ :=
  Finset.sum D.jumpRadii (fun a => ((-(D.jumpWeight a) : ℤ) + if a < D.t then D.jumpWeight a else 0))

/-- The finite jump data are realized when the recorded average equals the filtered threshold sum
minus the total reciprocal contribution. -/
def xi_ellipse_wallcrossing_realize_finite_jump_data_data.realizesFiniteJumpData
    (D : xi_ellipse_wallcrossing_realize_finite_jump_data_data) : Prop :=
  D.ellipseAverage =
      xi_ellipse_wallcrossing_realize_finite_jump_data_realizedEllipseAverage D ∧
    xi_ellipse_wallcrossing_realize_finite_jump_data_realizedEllipseAverage D =
      xi_ellipse_wallcrossing_realize_finite_jump_data_thresholdCrossingSum D -
        xi_ellipse_wallcrossing_realize_finite_jump_data_reciprocalPoleSum D

/-- Paper label: `prop:xi-ellipse-wallcrossing-realize-finite-jump-data`. -/
theorem paper_xi_ellipse_wallcrossing_realize_finite_jump_data
    (D : XiEllipseWallcrossingRealizeFiniteJumpData) : D.realizesFiniteJumpData := by
  refine ⟨D.ellipseAverage_eq, ?_⟩
  rw [xi_ellipse_wallcrossing_realize_finite_jump_data_realizedEllipseAverage,
    xi_ellipse_wallcrossing_realize_finite_jump_data_thresholdCrossingSum,
    xi_ellipse_wallcrossing_realize_finite_jump_data_reciprocalPoleSum]
  calc
    Finset.sum D.jumpRadii (fun a => ((-(D.jumpWeight a) : ℤ) + if a < D.t then D.jumpWeight a else 0))
        =
          Finset.sum D.jumpRadii (fun a => (-(D.jumpWeight a) : ℤ)) +
            Finset.sum D.jumpRadii (fun a => (if a < D.t then D.jumpWeight a else 0 : ℤ)) := by
          rw [Finset.sum_add_distrib]
    _ =
          -Finset.sum D.jumpRadii D.jumpWeight +
            Finset.sum D.jumpRadii (fun a => (if a < D.t then D.jumpWeight a else 0 : ℤ)) := by
          simp
    _ =
          -Finset.sum D.jumpRadii D.jumpWeight +
            Finset.sum (D.jumpRadii.filter fun a => a < D.t) D.jumpWeight := by
          rw [Finset.sum_filter]
    _ =
          Finset.sum (D.jumpRadii.filter fun a => a < D.t) D.jumpWeight -
            Finset.sum D.jumpRadii D.jumpWeight := by
          ring

end Omega.Zeta
