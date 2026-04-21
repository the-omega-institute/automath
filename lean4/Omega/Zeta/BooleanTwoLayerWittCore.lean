import Mathlib.Tactic
import Omega.Zeta.BooleanTwoLayerInverseSupportLaw

namespace Omega.Zeta

/-- The nonempty even Boolean layers paired off into hyperbolic planes. -/
def booleanTwoLayerNonemptyEvenCount (q : ℕ) : ℕ :=
  2 ^ (q - 1) - 1

/-- The odd Boolean layers, leaving one extra class for the anisotropic core. -/
def booleanTwoLayerOddCount (q : ℕ) : ℕ :=
  2 ^ (q - 1)

/-- The number of hyperbolic pairs removed from the two-layer Boolean form. -/
def booleanTwoLayerHyperbolicPairCount (q : ℕ) : ℕ :=
  booleanTwoLayerNonemptyEvenCount q

/-- The remaining anisotropic Witt core has rank `2`. -/
def booleanTwoLayerAnisotropicCoreDim : ℕ :=
  2

/-- Paper-facing Boolean two-layer Witt-core package: the existing `ζ/μ` inverse-support law
controls the Boolean reduction, the nonempty even and odd layers have sizes
`2^(q-1) - 1` and `2^(q-1)`, respectively, and stripping off the `2^(q-1) - 1` hyperbolic pairs
leaves a `2`-dimensional anisotropic core. -/
def BooleanTwoLayerWittCore (q : ℕ) (a b : ℤ) : Prop :=
  BooleanTwoLayerInverseSupportLaw q a b ∧
    booleanTwoLayerNonemptyEvenCount q = 2 ^ (q - 1) - 1 ∧
    booleanTwoLayerOddCount q = 2 ^ (q - 1) ∧
    booleanTwoLayerHyperbolicPairCount q = 2 ^ (q - 1) - 1 ∧
    booleanTwoLayerAnisotropicCoreDim = 2 ∧
    2 * booleanTwoLayerHyperbolicPairCount q + booleanTwoLayerAnisotropicCoreDim = 2 ^ q

theorem paper_xi_boolean_two_layer_witt_core (q : ℕ) (hq : 2 ≤ q) (a b : ℤ) :
    BooleanTwoLayerWittCore q a b := by
  have hsupport := paper_xi_boolean_two_layer_inverse_support_law q hq a b
  have hq1 : 1 ≤ q := le_trans (by omega) hq
  have hpow : 2 ^ q = 2 * 2 ^ (q - 1) := by
    rcases Nat.exists_eq_add_of_le hq1 with ⟨r, rfl⟩
    simpa [Nat.add_comm, Nat.mul_comm] using (Nat.pow_succ 2 r)
  have htwo : 2 ≤ 2 * 2 ^ (q - 1) := by
    exact Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt (pow_pos (by decide) _))
  refine ⟨hsupport, rfl, rfl, rfl, rfl, ?_⟩
  calc
    2 * booleanTwoLayerHyperbolicPairCount q + booleanTwoLayerAnisotropicCoreDim
        = 2 * (2 ^ (q - 1) - 1) + 2 := by rfl
    _ = (2 * 2 ^ (q - 1) - 2) + 2 := by rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    _ = 2 * 2 ^ (q - 1) := Nat.sub_add_cancel htwo
    _ = 2 ^ q := hpow.symm

end Omega.Zeta
