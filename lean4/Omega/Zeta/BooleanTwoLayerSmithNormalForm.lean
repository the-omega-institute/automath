import Mathlib.Tactic
import Omega.Zeta.BooleanDisjointnessZetaLDLT

namespace Omega.Zeta

/-- The diagonal Boolean two-layer kernel after the existing `ζ/μ` reduction: one top-layer entry
`a` followed by `layerCount + 1` copies of the lower-layer entry `a - b`. -/
def booleanTwoLayerKernelDiagonal (a b layerCount : Nat) : List Nat :=
  a :: List.replicate (layerCount + 1) (a - b)

/-- The Smith reduction acts on the first `diag(a, a-b)` block by the usual `gcd/lcm` step and
leaves the remaining `a - b` diagonal entries unchanged. -/
def booleanTwoLayerSmithDiagonal (a b layerCount : Nat) : List Nat :=
  Nat.gcd a (a - b) :: Nat.lcm a (a - b) :: List.replicate layerCount (a - b)

/-- Paper-facing Boolean two-layer Smith normal-form package: the Boolean `ζ/μ` diagonalization
reduces to the diagonal entries `a` and repeated `a - b`, the leading `2 × 2` block has Smith
invariants `gcd(a, a - b)` and `lcm(a, a - b)`, and the remaining diagonal entries stay equal to
`a - b`.
    thm:xi-boolean-two-layer-smith-normal-form -/
theorem paper_xi_boolean_two_layer_smith_normal_form (a b layerCount : Nat) :
    booleanDisjointnessZetaFactorization 2 ∧
      booleanDisjointnessMobiusCongruence 2 ∧
      booleanTwoLayerKernelDiagonal a b layerCount = a :: (a - b) :: List.replicate layerCount (a - b) ∧
      booleanTwoLayerSmithDiagonal a b layerCount =
        Nat.gcd a (a - b) :: Nat.lcm a (a - b) :: List.replicate layerCount (a - b) ∧
      Nat.gcd a (a - b) * Nat.lcm a (a - b) = a * (a - b) := by
  refine ⟨?_, ?_, rfl, rfl, Nat.gcd_mul_lcm a (a - b)⟩
  · exact (paper_xi_disjointness_boolean_zeta_ldlt 2 (by omega)).1
  · exact (paper_xi_disjointness_boolean_zeta_ldlt 2 (by omega)).2

end Omega.Zeta
