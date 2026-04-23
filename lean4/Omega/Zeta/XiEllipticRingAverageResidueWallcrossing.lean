import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Residue sum over the poles whose modulus is strictly smaller than `radius`. -/
def xi_elliptic_ring_average_residue_wallcrossing_residueSumBelow
    (poles : Finset ℂ) (residue : ℂ → ℂ) (radius : ℝ) : ℂ :=
  ∑ a ∈ poles.filter (fun a => ‖a‖ < radius), residue a

/-- Concrete finite residue data for the elliptic-ring wallcrossing package: every nonzero pole
lies on a single critical modulus, and the lower/upper chamber averages are written as residue
sums on the two sides of that wall. -/
structure xi_elliptic_ring_average_residue_wallcrossing_data where
  xi_elliptic_ring_average_residue_wallcrossing_poles : Finset ℂ
  xi_elliptic_ring_average_residue_wallcrossing_residue : ℂ → ℂ
  xi_elliptic_ring_average_residue_wallcrossing_zeroResidue : ℂ
  xi_elliptic_ring_average_residue_wallcrossing_lowerRadius : ℝ
  xi_elliptic_ring_average_residue_wallcrossing_criticalRadius : ℝ
  xi_elliptic_ring_average_residue_wallcrossing_upperRadius : ℝ
  xi_elliptic_ring_average_residue_wallcrossing_lowerAverage : ℂ
  xi_elliptic_ring_average_residue_wallcrossing_upperAverage : ℂ
  xi_elliptic_ring_average_residue_wallcrossing_lower_lt_critical :
    xi_elliptic_ring_average_residue_wallcrossing_lowerRadius <
      xi_elliptic_ring_average_residue_wallcrossing_criticalRadius
  xi_elliptic_ring_average_residue_wallcrossing_critical_lt_upper :
    xi_elliptic_ring_average_residue_wallcrossing_criticalRadius <
      xi_elliptic_ring_average_residue_wallcrossing_upperRadius
  xi_elliptic_ring_average_residue_wallcrossing_pole_modulus :
    ∀ a ∈ xi_elliptic_ring_average_residue_wallcrossing_poles,
      ‖a‖ = xi_elliptic_ring_average_residue_wallcrossing_criticalRadius
  xi_elliptic_ring_average_residue_wallcrossing_lowerAverage_eq :
    xi_elliptic_ring_average_residue_wallcrossing_lowerAverage =
      xi_elliptic_ring_average_residue_wallcrossing_zeroResidue +
        xi_elliptic_ring_average_residue_wallcrossing_residueSumBelow
          xi_elliptic_ring_average_residue_wallcrossing_poles
          xi_elliptic_ring_average_residue_wallcrossing_residue
          xi_elliptic_ring_average_residue_wallcrossing_lowerRadius
  xi_elliptic_ring_average_residue_wallcrossing_upperAverage_eq :
    xi_elliptic_ring_average_residue_wallcrossing_upperAverage =
      xi_elliptic_ring_average_residue_wallcrossing_zeroResidue +
        xi_elliptic_ring_average_residue_wallcrossing_residueSumBelow
          xi_elliptic_ring_average_residue_wallcrossing_poles
          xi_elliptic_ring_average_residue_wallcrossing_residue
          xi_elliptic_ring_average_residue_wallcrossing_upperRadius

namespace xi_elliptic_ring_average_residue_wallcrossing_data

/-- The residue contribution picked up exactly on the critical modulus. -/
def xi_elliptic_ring_average_residue_wallcrossing_criticalResidueSum
    (D : xi_elliptic_ring_average_residue_wallcrossing_data) : ℂ :=
  ∑ a ∈ D.xi_elliptic_ring_average_residue_wallcrossing_poles,
    D.xi_elliptic_ring_average_residue_wallcrossing_residue a

/-- Residue-theorem chamber formula for a radius just above the critical modulus. -/
def residueFormula (D : xi_elliptic_ring_average_residue_wallcrossing_data) : Prop :=
  D.xi_elliptic_ring_average_residue_wallcrossing_upperAverage =
    D.xi_elliptic_ring_average_residue_wallcrossing_zeroResidue +
      D.xi_elliptic_ring_average_residue_wallcrossing_criticalResidueSum

/-- The wallcrossing jump is exactly the sum of residues on the crossed critical circle. -/
def wallcrossingJumpFormula (D : xi_elliptic_ring_average_residue_wallcrossing_data) : Prop :=
  D.xi_elliptic_ring_average_residue_wallcrossing_upperAverage -
      D.xi_elliptic_ring_average_residue_wallcrossing_lowerAverage =
    D.xi_elliptic_ring_average_residue_wallcrossing_criticalResidueSum

end xi_elliptic_ring_average_residue_wallcrossing_data

/-- Paper label: `prop:xi-elliptic-ring-average-residue-wallcrossing`. The lower chamber contains
no nonzero poles, the upper chamber contains exactly the pole family on the critical modulus, so
the contour average equals the interior residue sum and the wallcrossing jump is the residue mass
on that critical circle. -/
theorem paper_xi_elliptic_ring_average_residue_wallcrossing
    (h : xi_elliptic_ring_average_residue_wallcrossing_data) :
    h.residueFormula /\ h.wallcrossingJumpFormula := by
  have hLowerFilter :
      h.xi_elliptic_ring_average_residue_wallcrossing_poles.filter
          (fun a => ‖a‖ < h.xi_elliptic_ring_average_residue_wallcrossing_lowerRadius) =
        ∅ := by
    apply Finset.ext
    intro a
    constructor
    · intro ha
      exfalso
      rcases Finset.mem_filter.mp ha with ⟨haPole, hlt⟩
      rw [h.xi_elliptic_ring_average_residue_wallcrossing_pole_modulus a haPole] at hlt
      exact (not_lt.mpr
        (le_of_lt h.xi_elliptic_ring_average_residue_wallcrossing_lower_lt_critical)) hlt
    · intro ha
      simp at ha
  have hUpperFilter :
      h.xi_elliptic_ring_average_residue_wallcrossing_poles.filter
          (fun a => ‖a‖ < h.xi_elliptic_ring_average_residue_wallcrossing_upperRadius) =
        h.xi_elliptic_ring_average_residue_wallcrossing_poles := by
    apply Finset.ext
    intro a
    constructor
    · intro ha
      exact (Finset.mem_filter.mp ha).1
    · intro ha
      refine Finset.mem_filter.mpr ⟨ha, ?_⟩
      rw [h.xi_elliptic_ring_average_residue_wallcrossing_pole_modulus a ha]
      exact h.xi_elliptic_ring_average_residue_wallcrossing_critical_lt_upper
  have hLowerAverage :
      h.xi_elliptic_ring_average_residue_wallcrossing_lowerAverage =
        h.xi_elliptic_ring_average_residue_wallcrossing_zeroResidue := by
    rw [h.xi_elliptic_ring_average_residue_wallcrossing_lowerAverage_eq,
      xi_elliptic_ring_average_residue_wallcrossing_residueSumBelow, hLowerFilter]
    simp
  have hUpperAverage :
      h.xi_elliptic_ring_average_residue_wallcrossing_upperAverage =
        h.xi_elliptic_ring_average_residue_wallcrossing_zeroResidue +
          h.xi_elliptic_ring_average_residue_wallcrossing_criticalResidueSum := by
    rw [h.xi_elliptic_ring_average_residue_wallcrossing_upperAverage_eq,
      xi_elliptic_ring_average_residue_wallcrossing_residueSumBelow, hUpperFilter]
    simp [xi_elliptic_ring_average_residue_wallcrossing_data.xi_elliptic_ring_average_residue_wallcrossing_criticalResidueSum]
  refine ⟨hUpperAverage, ?_⟩
  rw [xi_elliptic_ring_average_residue_wallcrossing_data.wallcrossingJumpFormula,
    hUpperAverage, hLowerAverage]
  ring

end

end Omega.Zeta
