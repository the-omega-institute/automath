import Omega.GU.BdrySymmetricGroupSignTwistedLabelD2
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic

namespace Omega.GU

private theorem perm_fin_pretransitive {d : ℕ} (s0 : Fin d) :
    IsTransitiveAction (Equiv.Perm (Fin d)) (Fin d) := by
  change MulAction.IsPretransitive (Equiv.Perm (Fin d)) (Fin d)
  rw [MulAction.isPretransitive_iff_base (G := Equiv.Perm (Fin d)) (X := Fin d) s0]
  intro x
  refine ⟨Equiv.swap s0 x, by simp⟩

/-- Paper label: `cor:terminal-cross-scale-binary-chirality-symmetry-breaking`.
The sign-twisted binary label exists for the two-point boundary fiber, but fails as soon as the
boundary fiber acquires three sheets: a transposition fixing the chosen basepoint already has sign
`-1`, contradicting stabilizer triviality. -/
theorem paper_terminal_cross_scale_binary_chirality_symmetry_breaking :
    chiTwistedBinaryLabelExists (Equiv.Perm (Fin 2)) (Fin 2) Equiv.Perm.sign /\
    ¬ chiTwistedBinaryLabelExists (Equiv.Perm (Fin 3)) (Fin 3) Equiv.Perm.sign := by
  refine ⟨chiTwistedBinaryLabelExists_perm_fin_two, ?_⟩
  intro hχ
  have hstab :=
    (paper_bdry_chi_twisted_binary_label_existence
      (Equiv.Perm (Fin 3)) (Fin 3) Equiv.Perm.sign (2 : Fin 3) (perm_fin_pretransitive 2)).1 hχ
  let g : Equiv.Perm (Fin 3) := Equiv.swap (0 : Fin 3) 1
  have hfix : g • (2 : Fin 3) = 2 := by
    decide
  have htriv : Equiv.Perm.sign g = 1 := hstab g hfix
  have hsign : Equiv.Perm.sign g = -1 := by
    dsimp [g]
    exact Equiv.Perm.sign_swap (by simp)
  have : (-1 : ℤˣ) = 1 := by
    calc
      (-1 : ℤˣ) = Equiv.Perm.sign g := hsign.symm
      _ = 1 := htriv
  norm_num at this

end Omega.GU
