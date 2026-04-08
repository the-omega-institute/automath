import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Decode a ZMod (2^N) element to its bit vector (Fin N → Bool).
    prop:cdim-dyadic-kernel-cube-inverse-limit -/
def zmodTwoPowToBool (N : ℕ) (a : ZMod (2^N)) : Fin N → Bool :=
  fun i => Nat.testBit a.val i.val

/-- Encode a bit vector back into ZMod (2^N).
    prop:cdim-dyadic-kernel-cube-inverse-limit -/
def boolToZmodTwoPow (N : ℕ) (b : Fin N → Bool) : ZMod (2^N) :=
  (∑ i : Fin N, if b i then 2^i.val else 0 : ℕ)

/-- Trivial bit vector at N = 0.
    prop:cdim-dyadic-kernel-cube-inverse-limit -/
theorem zmodTwoPowToBool_zero (a : ZMod (2^0)) :
    zmodTwoPowToBool 0 a = fun i : Fin 0 => i.elim0 := by
  funext i
  exact i.elim0

/-- Trivial encode at N = 0.
    prop:cdim-dyadic-kernel-cube-inverse-limit -/
theorem boolToZmodTwoPow_zero (b : Fin 0 → Bool) :
    boolToZmodTwoPow 0 b = 0 := by
  unfold boolToZmodTwoPow
  simp

/-- Cardinality of the Boolean cube of dimension N.
    prop:cdim-dyadic-kernel-cube-inverse-limit -/
theorem card_fin_bool (N : ℕ) :
    Fintype.card (Fin N → Bool) = 2^N := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

/-- Cardinality of ZMod (2^N).
    prop:cdim-dyadic-kernel-cube-inverse-limit -/
theorem card_zmod_two_pow (N : ℕ) :
    Fintype.card (ZMod (2^N)) = 2^N := by
  rw [ZMod.card]

/-- Paper-facing finite-truncation skeleton package.
    Full bijection round-trip deferred.
    prop:cdim-dyadic-kernel-cube-inverse-limit -/
theorem paper_cdim_dyadic_kernel_cube_finite_skeleton :
    (∀ N : ℕ, Fintype.card (ZMod (2^N)) = Fintype.card (Fin N → Bool)) ∧
    (∀ N : ℕ, Fintype.card (ZMod (2^N)) = 2^N) ∧
    (∀ N : ℕ, Fintype.card (Fin N → Bool) = 2^N) ∧
    (∀ (a : ZMod (2^0)), zmodTwoPowToBool 0 a = fun i : Fin 0 => i.elim0) ∧
    (∀ (b : Fin 0 → Bool), boolToZmodTwoPow 0 b = 0) := by
  refine ⟨?_, card_zmod_two_pow, card_fin_bool,
          zmodTwoPowToBool_zero, boolToZmodTwoPow_zero⟩
  intro N
  rw [card_zmod_two_pow, card_fin_bool]

end Omega.CircleDimension
