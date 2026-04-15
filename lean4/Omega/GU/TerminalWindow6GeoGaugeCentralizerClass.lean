import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

namespace Omega.GU

/-- Orbit-charge datum for a single window-`6` fiber in the gauge-centralizer audit. -/
structure Window6GeoGaugeOrbitCharge where
  fixedPoints : ℕ
  twoCycles : ℕ
  multiplicity : ℕ

/-- The centralizer factor contributed by the cycle type `1^f 2^p`. -/
def window6GeoGaugeCentralizerFactor (q : Window6GeoGaugeOrbitCharge) : ℕ :=
  q.fixedPoints.factorial * 2 ^ q.twoCycles * q.twoCycles.factorial

/-- The gauge-group factor contributed by a fiber of size `f + 2p`. -/
def window6GeoGaugeFactor (q : Window6GeoGaugeOrbitCharge) : ℕ :=
  (q.fixedPoints + 2 * q.twoCycles).factorial

/-- The orbit-charge histogram extracted from the generated audit table
    `tab_foldbin6_geo_orbit_charge.tex`. -/
def window6GeoGaugeOrbitChargeHistogram : List Window6GeoGaugeOrbitCharge :=
  [⟨0, 1, 4⟩, ⟨2, 0, 4⟩, ⟨1, 1, 2⟩, ⟨3, 0, 2⟩, ⟨0, 2, 3⟩, ⟨2, 1, 4⟩, ⟨4, 0, 2⟩]

/-- Centralizer size obtained by multiplying the symmetric-group centralizer factors
    over the orbit-charge histogram. -/
def window6GeoGaugeCentralizer : ℕ :=
  (window6GeoGaugeOrbitChargeHistogram.map
    fun q => window6GeoGaugeCentralizerFactor q ^ q.multiplicity).prod

/-- Total discrete gauge-group size `∏_x d_x!`. -/
def window6GeoGaugeGroupSize : ℕ :=
  (window6GeoGaugeOrbitChargeHistogram.map fun q => window6GeoGaugeFactor q ^ q.multiplicity).prod

/-- The conjugacy-class index `|G_6^bin : C_G(g)|`. -/
def window6GeoGaugeConjugacyClassIndex : ℕ :=
  window6GeoGaugeGroupSize / window6GeoGaugeCentralizer

/-- Paper-facing wrapper for the window-`6` geometric gauge centralizer class.
    thm:terminal-window6-geo-gauge-centralizer-class -/
theorem paper_terminal_window6_geo_gauge_centralizer_class :
    window6GeoGaugeCentralizer = 2783138807808 ∧
      window6GeoGaugeGroupSize = ((2 : ℕ).factorial) ^ 8 * ((3 : ℕ).factorial) ^ 4 *
        ((4 : ℕ).factorial) ^ 9 ∧
      window6GeoGaugeGroupSize = 876488338465357824 ∧
      window6GeoGaugeConjugacyClassIndex = 314928 ∧
      window6GeoGaugeGroupSize =
        window6GeoGaugeCentralizer * window6GeoGaugeConjugacyClassIndex := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num [window6GeoGaugeCentralizer, window6GeoGaugeOrbitChargeHistogram,
      window6GeoGaugeCentralizerFactor]
  · norm_num [window6GeoGaugeGroupSize, window6GeoGaugeOrbitChargeHistogram,
      window6GeoGaugeFactor]
  · norm_num [window6GeoGaugeGroupSize, window6GeoGaugeOrbitChargeHistogram,
      window6GeoGaugeFactor]
  · norm_num [window6GeoGaugeConjugacyClassIndex, window6GeoGaugeGroupSize,
      window6GeoGaugeCentralizer, window6GeoGaugeOrbitChargeHistogram, window6GeoGaugeFactor,
      window6GeoGaugeCentralizerFactor]
  · norm_num [window6GeoGaugeConjugacyClassIndex, window6GeoGaugeGroupSize,
      window6GeoGaugeCentralizer, window6GeoGaugeOrbitChargeHistogram, window6GeoGaugeFactor,
      window6GeoGaugeCentralizerFactor]

end Omega.GU
