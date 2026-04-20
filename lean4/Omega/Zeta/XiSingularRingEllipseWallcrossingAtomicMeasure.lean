import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- The cumulative radial wallcrossing produced by a finite atomic residue family. -/
noncomputable def xiSingularRingCumulative (atoms : Finset ℝ) (jump : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ r ∈ atoms.filter (fun r => r < t), jump r

/-- The mass assigned to the annulus `(a, b)` is the difference of cumulative wallcrossing
values. -/
noncomputable def xiSingularRingAnnulusMass (atoms : Finset ℝ) (jump : ℝ → ℝ)
    (a b : ℝ) : ℝ :=
  xiSingularRingCumulative atoms jump b - xiSingularRingCumulative atoms jump a

/-- Annulus masses are obtained by subtracting cumulative residue sums between radii. -/
def xiSingularRingWallcrossingDifferenceLaw (atoms : Finset ℝ) (jump : ℝ → ℝ) : Prop :=
  ∀ a b, xiSingularRingAnnulusMass atoms jump a b =
    xiSingularRingCumulative atoms jump b - xiSingularRingCumulative atoms jump a

/-- Agreement of all annulus masses, together with the same base mass at radius `0`, forces the
cumulative wallcrossing functions to coincide. -/
def xiSingularRingAtomicMeasureUniqueness (atoms : Finset ℝ) : Prop :=
  ∀ jump jump' : ℝ → ℝ,
    xiSingularRingCumulative atoms jump 0 = xiSingularRingCumulative atoms jump' 0 →
    (∀ a b, xiSingularRingAnnulusMass atoms jump a b = xiSingularRingAnnulusMass atoms jump' a b) →
    ∀ t, xiSingularRingCumulative atoms jump t = xiSingularRingCumulative atoms jump' t

/-- The cumulative wallcrossing is reconstructed from the interval mass between radius `0` and the
target radius. -/
def xiSingularRingReconstructionFromJumps (atoms : Finset ℝ) (jump : ℝ → ℝ) : Prop :=
  ∀ t, xiSingularRingCumulative atoms jump t =
    xiSingularRingCumulative atoms jump 0 + xiSingularRingAnnulusMass atoms jump 0 t

/-- The radial residue package is a finite atomic measure: annulus masses are cumulative
differences, those interval masses determine the cumulative law once the base mass is fixed, and
the cumulative wallcrossing is recovered from the jump masses.
    prop:xi-singular-ring-ellipse-wallcrossing-atomic-measure -/
theorem paper_xi_singular_ring_ellipse_wallcrossing_atomic_measure
    (atoms : Finset ℝ) (jump : ℝ → ℝ) :
    xiSingularRingWallcrossingDifferenceLaw atoms jump ∧
      xiSingularRingAtomicMeasureUniqueness atoms ∧
      xiSingularRingReconstructionFromJumps atoms jump := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    rfl
  · intro jump₁ jump₂ hzero hinterval t
    have hdiff := hinterval 0 t
    dsimp [xiSingularRingAnnulusMass] at hdiff
    linarith
  · intro t
    dsimp [xiSingularRingAnnulusMass]
    ring

end Omega.Zeta
