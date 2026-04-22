import Mathlib.GroupTheory.Perm.Closure
import Mathlib.GroupTheory.Perm.Cycle.Type

namespace Omega.CircleDimension

/-- Paper label: `thm:cdim-s4-v4-deck-and-bielliptic-involution-generate-s3`.
On the three-pencil packet, a nontrivial involution and a nontrivial cubic deck transformation
satisfying the dihedral conjugation relation generate all of `S₃`. -/
theorem paper_cdim_s4_v4_deck_and_bielliptic_involution_generate_s3
    (sigma tau : Equiv.Perm (Fin 3)) (hsigma : sigma * sigma = 1) (htau : tau ^ 3 = 1)
    (hconj : sigma * tau * sigma = tau⁻¹) (hsigma_ne : sigma ≠ 1) (htau_ne : tau ≠ 1) :
    Subgroup.closure ({sigma, tau} : Set (Equiv.Perm (Fin 3))) = ⊤ := by
  have hsigma_order : orderOf sigma = 2 := orderOf_eq_prime hsigma hsigma_ne
  have hsigma_cycle : sigma.IsCycle :=
    Equiv.Perm.isCycle_of_prime_order'
      ((congrArg Nat.Prime hsigma_order).mpr (by decide))
      (by rw [hsigma_order]; decide)
  have hsigma_swap : sigma.IsSwap := by
    rw [← Equiv.Perm.card_support_eq_two]
    exact hsigma_cycle.orderOf.symm.trans hsigma_order
  have htau_order : orderOf tau = 3 := orderOf_eq_prime htau htau_ne
  have htau_cycle : tau.IsCycle :=
    Equiv.Perm.isCycle_of_prime_order'' (by decide) htau_order
  have htau_support : tau.support = Finset.univ :=
    Finset.eq_univ_of_card tau.support (htau_cycle.orderOf.symm.trans htau_order)
  let _ := hconj
  have hclosure :
      Subgroup.closure ({tau, sigma} : Set (Equiv.Perm (Fin 3))) = ⊤ :=
    Equiv.Perm.closure_prime_cycle_swap
      (σ := tau) (τ := sigma) (by decide) htau_cycle htau_support hsigma_swap
  have hswap :
      ({tau, sigma} : Set (Equiv.Perm (Fin 3))) = ({sigma, tau} : Set (Equiv.Perm (Fin 3))) := by
    ext π
    simp [or_comm]
  rw [hswap] at hclosure
  exact hclosure

end Omega.CircleDimension
