import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.ZMod.Basic

namespace Omega

/-- Any unital ring automorphism of `ZMod (F_{m+2})` is the identity, since it fixes `1` and hence
every natural residue class. `thm:fold-mod-semirings-unital-automorphism-rigidity` -/
theorem paper_fold_mod_semirings_unital_automorphism_rigidity (m : ℕ) :
    ∀ σ : ZMod (Nat.fib (m + 2)) ≃+* ZMod (Nat.fib (m + 2)), σ = RingEquiv.refl _ := by
  intro σ
  letI : NeZero (Nat.fib (m + 2)) := ⟨Nat.ne_of_gt (Nat.fib_pos.2 (by omega))⟩
  apply RingEquiv.ext
  intro x
  calc
    σ x = σ (x.val : ZMod (Nat.fib (m + 2))) := by rw [ZMod.natCast_zmod_val x]
    _ = (x.val : ZMod (Nat.fib (m + 2))) := by rw [map_natCast]
    _ = x := by rw [ZMod.natCast_zmod_val x]

end Omega
