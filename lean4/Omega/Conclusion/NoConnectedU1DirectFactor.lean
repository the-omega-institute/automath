import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete decomposition data for the connected automorphism group as a finite product of
projective unitary blocks. The field `blockDims` records the dimensions `d` of the `PU(d)`
factors, and the standing hypothesis says that every simple block has `d ≥ 2`. -/
structure ConnectedAutomorphismDecompositionData where
  blockDims : Finset ℕ
  blockDims_ge_two : ∀ d ∈ blockDims, 2 ≤ d

namespace ConnectedAutomorphismDecompositionData

/-- The real Lie-algebra dimension of the simple summand `su(d)`. -/
def lieSummandDimension (_D : ConnectedAutomorphismDecompositionData) (d : ℕ) : ℕ :=
  d ^ 2 - 1

/-- A connected `U(1)` direct factor would contribute a one-dimensional abelian Lie ideal. -/
def hasConnectedU1DirectFactor (D : ConnectedAutomorphismDecompositionData) : Prop :=
  ∃ d ∈ D.blockDims, D.lieSummandDimension d = 1

/-- In the `PU(d)` product decomposition, this obstruction is absent. -/
def noConnectedU1DirectFactor (D : ConnectedAutomorphismDecompositionData) : Prop :=
  ¬ D.hasConnectedU1DirectFactor

lemma lieSummandDimension_ge_three (D : ConnectedAutomorphismDecompositionData) {d : ℕ}
    (hd : 2 ≤ d) : 3 ≤ D.lieSummandDimension d := by
  have hmul : 4 ≤ d * d := by
    have : 2 * 2 ≤ d * d := Nat.mul_le_mul hd hd
    simpa using this
  have hsub : 3 ≤ d * d - 1 := by omega
  simpa [lieSummandDimension, pow_two] using hsub

end ConnectedAutomorphismDecompositionData

open ConnectedAutomorphismDecompositionData

/-- Paper label: `thm:conclusion-no-connected-u1-direct-factor`. Since every connected factor is a
`PU(d)` block with `d ≥ 2`, the Lie algebra is a direct sum of `su(d)` summands, each of
dimension at least `3`; hence no one-dimensional abelian Lie ideal, and therefore no connected
`U(1)` direct factor, can occur. -/
theorem paper_conclusion_no_connected_u1_direct_factor
    (D : ConnectedAutomorphismDecompositionData) : D.noConnectedU1DirectFactor := by
  intro hU1
  rcases hU1 with ⟨d, hd, hdim⟩
  have hlarge : 3 ≤ D.lieSummandDimension d :=
    D.lieSummandDimension_ge_three (D.blockDims_ge_two d hd)
  omega

end Omega.Conclusion
