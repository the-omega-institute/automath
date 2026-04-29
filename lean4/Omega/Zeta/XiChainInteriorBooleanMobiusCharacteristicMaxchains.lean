import Mathlib.Data.Fintype.Perm
import Omega.Zeta.XiChainInteriorBooleanFlagClosedForm

namespace Omega.Zeta

open Finset

/-- Concrete Boolean-lattice package for the chain interior: closed-form Boolean flags, the
interval Möbius sign, the binomial characteristic polynomial, and the permutation count of maximal
chains on the `n - 1` free coordinates. -/
def xi_chain_interior_boolean_mobius_characteristic_maxchains_package (n : Nat) : Prop :=
  let m := n - 1
  XiChainInteriorBooleanFlagClosedForm n ∧
    Fintype.card (Finset (Fin m)) = 2 ^ m ∧
    (∀ S T : Finset (Fin m), S ⊆ T → booleanIntervalSign S T = (-1 : ℤ) ^ (T.card - S.card)) ∧
    (∀ q : ℤ, ∑ S : Finset (Fin m), q ^ S.card = (q + 1) ^ m) ∧
    Fintype.card (Equiv.Perm (Fin m)) = Nat.factorial m

/-- Paper label: `thm:xi-chain-interior-boolean-mobius-characteristic-maxchains`. The existing
Boolean-flag closed form supplies the Boolean-rank, interval Möbius sign, and characteristic
polynomial, and maximal chains are counted by permutations of the `n - 1` free coordinates. -/
theorem paper_xi_chain_interior_boolean_mobius_characteristic_maxchains (n : Nat) :
    xi_chain_interior_boolean_mobius_characteristic_maxchains_package n := by
  let m := n - 1
  have hFlag := paper_xi_chain_interior_boolean_flag_closed_form n
  dsimp [xi_chain_interior_boolean_mobius_characteristic_maxchains_package, m]
  refine ⟨hFlag, hFlag.2.1, hFlag.2.2.2.2, hFlag.2.2.1, ?_⟩
  simpa [m] using (Fintype.card_perm (α := Fin m))

end Omega.Zeta
