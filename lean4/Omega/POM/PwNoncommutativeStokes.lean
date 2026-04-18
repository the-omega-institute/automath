import Mathlib.Tactic

namespace Omega.POM

/-- A finite cochain complex for the noncommutative Stokes package: a `TwoChain` has a boundary in
some boundary type, and the anomaly is evaluated on that boundary. -/
structure PWCochainComplex where
  TwoChain : Type
  BoundaryChain : Type
  boundary : TwoChain → BoundaryChain
  anomaly : BoundaryChain → ℤ

namespace PWCochainComplex

/-- Pair the anomaly `2`-cochain with a `TwoChain` by evaluating the anomaly on its boundary. -/
def pairAnomaly2Cochain (K : PWCochainComplex) (Sigma : K.TwoChain) : ℤ :=
  K.anomaly (K.boundary Sigma)

end PWCochainComplex

open PWCochainComplex

/-- Paper-facing noncommutative Stokes identity for the finite `PW` model: the anomaly on the
boundary agrees with the chain-cochain pairing by definition of the pairing.
    thm:pom-pw-noncommutative-stokes -/
theorem paper_pom_pw_noncommutative_stokes (K : PWCochainComplex) (Sigma : K.TwoChain) :
    K.anomaly (K.boundary Sigma) = K.pairAnomaly2Cochain Sigma := by
  rfl

end Omega.POM
