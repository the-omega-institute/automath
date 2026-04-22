import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.GU

/-- The unique nonzero `S₃`-invariant vector in `(𝔽₂)^3` is the constant-one vector.
    prop:bdry-three-axis-unique-symmetric-central-invariant -/
theorem paper_bdry_three_axis_unique_symmetric_central_invariant :
    ∃! z : Fin 3 → ZMod 2, z ≠ 0 ∧ ∀ σ : Equiv.Perm (Fin 3), z ∘ σ = z := by
  refine ⟨fun _ => (1 : ZMod 2), ?_, ?_⟩
  · constructor
    · intro hzero
      have hval := congrArg (fun f : Fin 3 → ZMod 2 => f 0) hzero
      simp at hval
    · intro σ
      funext i
      simp
  · intro z hz
    rcases hz with ⟨hz_ne_zero, hsymm⟩
    have h01raw := hsymm (Equiv.swap 0 1)
    have h12raw := hsymm (Equiv.swap 1 2)
    have h01 : z 1 = z 0 := by
      have h := congrArg (fun f : Fin 3 → ZMod 2 => f 0) h01raw
      simpa using h
    have h12 : z 2 = z 1 := by
      have h := congrArg (fun f : Fin 3 → ZMod 2 => f 1) h12raw
      simpa using h
    have hz0_ne : z 0 ≠ 0 := by
      intro hz0
      apply hz_ne_zero
      ext i
      fin_cases i
      · exact hz0
      · simpa [hz0] using h01
      · have hz1 : z 1 = 0 := by simpa [hz0] using h01
        simpa [hz1] using h12
    have hvals : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by
      decide
    have h0vals : z 0 = 0 ∨ z 0 = 1 := hvals (z 0)
    have h0one : z 0 = 1 := h0vals.resolve_left hz0_ne
    have h1one : z 1 = 1 := h01.trans h0one
    have h2one : z 2 = 1 := h12.trans h1one
    ext i
    fin_cases i
    · exact h0one
    · exact h1one
    · exact h2one

end Omega.GU
