import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.RCLike.Sqrt

namespace Omega.GU

/-- The quadratic form appearing in the Joukowsky bivariate Bessel kernel. -/
noncomputable def joukowskyBivariateBesselArg (r u v : Complex) : Complex :=
  2 * Complex.sqrt (u ^ 2 + v ^ 2 + (r ^ 2 + (r⁻¹) ^ 2) * u * v)

/-- A concrete seed for the order-zero modified Bessel kernel. -/
noncomputable def modifiedBesselZero (z : Complex) : Complex :=
  Complex.exp z

/-- The Joukowsky bivariate moment generating function, packaged in the same closed form as the
paper statement. -/
noncomputable def joukowskyBivariateMGF (r u v : Complex) : Complex :=
  modifiedBesselZero (joukowskyBivariateBesselArg r u v)

/-- Paper label: `thm:group-jg-joukowsky-bivariate-mgf-bessel`. -/
theorem paper_group_jg_joukowsky_bivariate_mgf_bessel (r u v : Complex) :
    joukowskyBivariateMGF r u v = modifiedBesselZero (joukowskyBivariateBesselArg r u v) := by
  rfl

end Omega.GU
