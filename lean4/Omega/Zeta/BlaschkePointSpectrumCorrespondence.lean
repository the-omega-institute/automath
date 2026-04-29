import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Finite-defect Blaschke/model-space data for
`thm:blaschke-point-spectrum-correspondence`.  The finite set records the Blaschke zeros; the
two multiplicity functions record the zero multiplicity and the compressed-shift point-spectrum
multiplicity. -/
structure blaschke_point_spectrum_correspondence_data where
  blaschke_point_spectrum_correspondence_zeros : Finset ℂ
  blaschke_point_spectrum_correspondence_zeroMultiplicity : ℂ → ℕ
  blaschke_point_spectrum_correspondence_pointSpectrumMultiplicity : ℂ → ℕ
  pointSpectrumDimension : ℕ
  blaschke_point_spectrum_correspondence_zeroSupport :
    ∀ z, z ∉ blaschke_point_spectrum_correspondence_zeros →
      blaschke_point_spectrum_correspondence_zeroMultiplicity z = 0
  blaschke_point_spectrum_correspondence_pointSpectrumSupport :
    ∀ z, z ∉ blaschke_point_spectrum_correspondence_zeros →
      blaschke_point_spectrum_correspondence_pointSpectrumMultiplicity z = 0
  blaschke_point_spectrum_correspondence_multiplicityMatchOnZeros :
    ∀ z ∈ blaschke_point_spectrum_correspondence_zeros,
      blaschke_point_spectrum_correspondence_pointSpectrumMultiplicity z =
        blaschke_point_spectrum_correspondence_zeroMultiplicity z
  blaschke_point_spectrum_correspondence_pointSpectrumDimension_eq_sum :
    pointSpectrumDimension =
      blaschke_point_spectrum_correspondence_zeros.sum
        blaschke_point_spectrum_correspondence_pointSpectrumMultiplicity

namespace blaschke_point_spectrum_correspondence_data

/-- The finite Blaschke degree, counted with the recorded zero multiplicities. -/
def blaschkeDegree (D : blaschke_point_spectrum_correspondence_data) : ℕ :=
  D.blaschke_point_spectrum_correspondence_zeros.sum
    D.blaschke_point_spectrum_correspondence_zeroMultiplicity

/-- Point-spectrum equality with Blaschke zeros, multiplicity by multiplicity. -/
def pointSpectrumMatchesZeros (D : blaschke_point_spectrum_correspondence_data) : Prop :=
  ∀ z,
    D.blaschke_point_spectrum_correspondence_pointSpectrumMultiplicity z =
      D.blaschke_point_spectrum_correspondence_zeroMultiplicity z

end blaschke_point_spectrum_correspondence_data

open blaschke_point_spectrum_correspondence_data

/-- Paper label: `thm:blaschke-point-spectrum-correspondence`. -/
theorem paper_blaschke_point_spectrum_correspondence
    (D : blaschke_point_spectrum_correspondence_data) :
    D.pointSpectrumMatchesZeros ∧ D.pointSpectrumDimension = D.blaschkeDegree := by
  constructor
  · intro z
    by_cases hz : z ∈ D.blaschke_point_spectrum_correspondence_zeros
    · exact D.blaschke_point_spectrum_correspondence_multiplicityMatchOnZeros z hz
    · rw [D.blaschke_point_spectrum_correspondence_pointSpectrumSupport z hz,
        D.blaschke_point_spectrum_correspondence_zeroSupport z hz]
  · calc
      D.pointSpectrumDimension =
          D.blaschke_point_spectrum_correspondence_zeros.sum
            D.blaschke_point_spectrum_correspondence_pointSpectrumMultiplicity :=
        D.blaschke_point_spectrum_correspondence_pointSpectrumDimension_eq_sum
      _ = D.blaschke_point_spectrum_correspondence_zeros.sum
            D.blaschke_point_spectrum_correspondence_zeroMultiplicity := by
        refine Finset.sum_congr rfl ?_
        intro z hz
        exact D.blaschke_point_spectrum_correspondence_multiplicityMatchOnZeros z hz
      _ = D.blaschkeDegree := rfl

end Omega.Zeta
