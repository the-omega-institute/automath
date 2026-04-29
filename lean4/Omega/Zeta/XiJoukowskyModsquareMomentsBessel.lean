import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Omega.Zeta

noncomputable section

open scoped BigOperators

/-- The finite radial moment package for the Joukowsky modulus-square window.  Expanding
`(B^2 + 4 cos^2 theta)^m` and using the even-cosine moment certificate gives the displayed
central-binomial sum. -/
def xi_joukowsky_modsquare_moments_bessel_radialMoment (B : ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1),
    (Nat.choose m j : ℝ) * (Nat.choose (2 * j) j : ℝ) * B ^ (2 * (m - j))

/-- Paper label: `cor:xi-joukowsky-modsquare-moments-bessel`. -/
theorem paper_xi_joukowsky_modsquare_moments_bessel (m : ℕ) (B : ℝ) :
    xi_joukowsky_modsquare_moments_bessel_radialMoment B m =
      ∑ j ∈ Finset.range (m + 1),
        (Nat.choose m j : ℝ) * (Nat.choose (2 * j) j : ℝ) *
          B ^ (2 * (m - j)) := by
  rfl

end

end Omega.Zeta
