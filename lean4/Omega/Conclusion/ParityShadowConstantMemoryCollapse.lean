import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Once all nine parity channels share eventual period `16`, the full parity shadow is a
tail-finite-state function of the residue class modulo `16`.
    prop:conclusion-parity-shadow-constant-memory-collapse -/
theorem paper_conclusion_parity_shadow_constant_memory_collapse
    (s : ℕ → Fin 9 → ZMod 2) (m0 : ℕ)
    (hperiodic : ∀ i : Fin 9, ∀ n : ℕ, s (m0 + n + 16) i = s (m0 + n) i) :
    ∃ F : ZMod 16 → (Fin 9 → ZMod 2), ∀ m ≥ m0, s m = F (m : ZMod 16) := by
  have hperiodic_iter :
      ∀ q n : ℕ, s (m0 + n + 16 * q) = s (m0 + n) := by
    intro q n
    induction q with
    | zero =>
        simp
    | succ q ih =>
        ext i
        calc
          s (m0 + n + 16 * (q + 1)) i = s (m0 + (n + 16 * q) + 16) i := by
            ring_nf
          _ = s (m0 + (n + 16 * q)) i := by
              simpa [add_assoc, add_left_comm, add_comm] using hperiodic i (n + 16 * q)
          _ = s (m0 + n) i := by
              simpa [add_assoc, add_left_comm, add_comm] using congrFun ih i
  let F : ZMod 16 → (Fin 9 → ZMod 2) :=
    fun z => s (m0 + ((z.val + (16 - m0 % 16)) % 16))
  refine ⟨F, ?_⟩
  intro m hm
  have hdecomp : m = m0 + ((m - m0) % 16) + 16 * ((m - m0) / 16) := by
    have hsplit := Nat.mod_add_div (m - m0) 16
    omega
  have hres :
      (((m : ZMod 16)).val + (16 - m0 % 16)) % 16 = (m - m0) % 16 := by
    rw [ZMod.val_natCast]
    omega
  have hcollapse :
      s (m0 + ((m - m0) % 16) + 16 * ((m - m0) / 16)) = s (m0 + ((m - m0) % 16)) := by
    simpa [add_assoc, add_left_comm, add_comm] using
      hperiodic_iter ((m - m0) / 16) ((m - m0) % 16)
  calc
    s m = s (m0 + ((m - m0) % 16) + 16 * ((m - m0) / 16)) := by
          simpa using congrArg s hdecomp
    _ = s (m0 + ((m - m0) % 16)) := hcollapse
    _ = F (m : ZMod 16) := by
          simp only [F]
          congr 1
          simpa using congrArg (fun t : Nat => m0 + t) hres.symm

end Omega.Conclusion
