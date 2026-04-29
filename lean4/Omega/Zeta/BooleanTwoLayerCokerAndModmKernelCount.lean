import Mathlib.Tactic
import Omega.Zeta.BooleanTwoLayerSmithNormalForm

namespace Omega.Zeta

/-- The cyclic factors of the Boolean two-layer cokernel are the Smith diagonal entries. -/
def booleanTwoLayerCokernelFactors (a b layerCount : Nat) : List Nat :=
  booleanTwoLayerSmithDiagonal a b layerCount

/-- The mod-`m` kernel size of the Smith diagonal is the product of the coordinatewise gcd
contributions. -/
def booleanTwoLayerModKernelCount (a b layerCount m : Nat) : Nat :=
  ((booleanTwoLayerCokernelFactors a b layerCount).map (Nat.gcd m)).prod

/-- Paper-facing cokernel decomposition and mod-`m` kernel count for the Boolean two-layer matrix:
the Smith factors from `paper_xi_boolean_two_layer_smith_normal_form` give the cyclic cokernel
summands, and reducing modulo `m` multiplies the coordinatewise gcd contributions.
    prop:xi-boolean-two-layer-coker-and-modm-kernel-count -/
theorem paper_xi_boolean_two_layer_coker_and_modm_kernel_count
    (a b q m : Nat) :
    booleanTwoLayerCokernelFactors a b (2 ^ q - 2) =
      Nat.gcd a (a - b) :: Nat.lcm a (a - b) :: List.replicate (2 ^ q - 2) (a - b) ∧
    booleanTwoLayerModKernelCount a b (2 ^ q - 2) m =
      Nat.gcd m (Nat.gcd a (a - b)) * Nat.gcd m (Nat.lcm a (a - b)) *
        Nat.gcd m (a - b) ^ (2 ^ q - 2) := by
  have _ := paper_xi_boolean_two_layer_smith_normal_form a b (2 ^ q - 2)
  dsimp [booleanTwoLayerCokernelFactors, booleanTwoLayerModKernelCount]
  constructor
  · rfl
  · simp [booleanTwoLayerSmithDiagonal, Nat.mul_assoc]

end Omega.Zeta
