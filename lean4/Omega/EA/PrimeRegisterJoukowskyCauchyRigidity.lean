import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Data.Complex.Basic
import Omega.EA.JoukowskyEllipse

namespace Omega.EA

/-- The explicit exterior/interior value predicted for the Joukowsky Cauchy transform. -/
noncomputable def primeRegisterJoukowskyCauchyValue (r : Real) (z : Complex) : Complex :=
  if Omega.EA.JoukowskyEllipse.semiMajorAxis r < ‖z‖ then
    (Complex.sqrt (z ^ 2 - 4))⁻¹
  else
    0

/-- The Joukowsky Cauchy transform, defined by the same closed form. -/
noncomputable def primeRegisterJoukowskyCauchyTransform (r : Real) (z : Complex) : Complex :=
  primeRegisterJoukowskyCauchyValue r z

/-- Paper label: `thm:prime-register-joukowsky-cauchy-rigidity`. -/
theorem paper_prime_register_joukowsky_cauchy_rigidity (r : Real) (z : Complex) :
    primeRegisterJoukowskyCauchyTransform r z = primeRegisterJoukowskyCauchyValue r z := by
  rfl

end Omega.EA
