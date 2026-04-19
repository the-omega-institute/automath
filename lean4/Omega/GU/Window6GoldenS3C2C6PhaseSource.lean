import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic

namespace Omega.GU

/-- A concrete `S₃ × C₂` witness whose permutation part is a `3`-cycle and whose parity part is
the nontrivial element of `C₂`, hence the combined element has order `6`.
    cor:window6-golden-s3c2-c6-phase-source -/
theorem paper_window6_golden_s3c2_c6_phase_source :
    ∃ g : Equiv.Perm (Fin 3) × Multiplicative (ZMod 2),
      g ^ 6 = 1 ∧ g ^ 3 ≠ 1 ∧ g ^ 2 ≠ 1 := by
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
  let ε : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1
  have hσ3 : σ ^ 3 = 1 := by
    ext x
    fin_cases x <;> rfl
  have hσ6 : σ ^ 6 = 1 := by
    calc
      σ ^ 6 = (σ ^ 3) ^ 2 := by rw [show 6 = 3 * 2 by decide, pow_mul]
      _ = 1 := by simp [hσ3]
  have hε6 : ε ^ 6 = 1 := by
    change (0 : ZMod 2) = 0
    decide
  refine ⟨(σ, ε), ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · change (σ ^ 6, ε ^ 6) = (1, 1)
    exact Prod.ext hσ6 hε6
  · intro h
    have hsnd := congrArg Prod.snd h
    change (1 : ZMod 2) = 0 at hsnd
    norm_num at hsnd
  · intro h
    have hfst := congrArg Prod.fst h
    have h0 := congrArg (fun τ => τ 0) hfst
    have h02 : ((Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) ^ 2) 0 = 2 := by
      rfl
    have hbad : (2 : Fin 3) = 0 := h02.symm.trans h0
    exact (by decide : (2 : Fin 3) ≠ 0) hbad

end Omega.GU
