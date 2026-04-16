import Mathlib.Tactic
import Omega.GU.TerminalWindow6GeoFixedSubalgebraWedderburn

namespace Omega.GU

/-- Total number of fixed points contributed by the window-6 geometric orbit-charge histogram. -/
def window6GeoTotalFixedPoints : Nat :=
  window6GeoOrbitChargeHistogram.foldl (fun acc c => acc + c.multiplicity * c.fixedPoints) 0

/-- Total number of `2`-cycles contributed by the window-6 geometric orbit-charge histogram. -/
def window6GeoTotalTwoCycles : Nat :=
  window6GeoOrbitChargeHistogram.foldl (fun acc c => acc + c.multiplicity * c.twoCycles) 0

/-- Dimension of the permutation representation `ℂ^{Ω₆}` recovered from the cycle census. -/
def window6GeoPermutationRepresentationDim : Nat :=
  window6GeoTotalFixedPoints + 2 * window6GeoTotalTwoCycles

/-- The `(-1)`-eigenspace dimension equals the number of swapped pairs. -/
def window6GeoSignAntiinvariantDim : Nat :=
  window6GeoTotalTwoCycles

/-- Canonical antisymmetric basis indexed by the `2`-cycle orbits. -/
abbrev Window6GeoSignAntiinvariantBasis : Type :=
  Fin window6GeoSignAntiinvariantDim

/-- Paper wrapper: the audited orbit-charge histogram yields `32` fixed points and `16`
two-cycles, so the permutation representation has dimension `64` and its antisymmetric
sign-isotypic component has the canonical `16`-element basis indexed by the `2`-cycles.
    thm:terminal-foldbin6-geo-sign-antiinvariant-16 -/
theorem paper_terminal_foldbin6_geo_sign_antiinvariant_16 :
    window6GeoTotalFixedPoints = 32 ∧
      window6GeoTotalTwoCycles = 16 ∧
      window6GeoPermutationRepresentationDim = 64 ∧
      window6GeoSignAntiinvariantDim = 16 ∧
      Fintype.card Window6GeoSignAntiinvariantBasis = 16 := by
  native_decide

end Omega.GU
