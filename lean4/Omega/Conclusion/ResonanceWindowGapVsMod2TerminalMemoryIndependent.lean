import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-resonance-window-gap-vs-mod2-terminal-memory-independent`. -/
theorem paper_conclusion_resonance_window_gap_vs_mod2_terminal_memory_independent
    (Delta Per : Nat → Nat)
    (hD2 : Delta 9 = Delta 11)
    (hP2 : Per 9 ≠ Per 11)
    (hD4 : Delta 15 = Delta 17)
    (hP4 : Per 15 ≠ Per 17) :
    ¬ ∃ F : Nat → Nat,
      Per 9 = F (Delta 9) ∧ Per 11 = F (Delta 11) ∧
        Per 15 = F (Delta 15) ∧ Per 17 = F (Delta 17) := by
  rintro ⟨F, h9, h11, h15, h17⟩
  have hEq4 : Per 15 = Per 17 := by
    calc
      Per 15 = F (Delta 15) := h15
      _ = F (Delta 17) := by rw [hD4]
      _ = Per 17 := h17.symm
  have _ : False := hP4 hEq4
  apply hP2
  calc
    Per 9 = F (Delta 9) := h9
    _ = F (Delta 11) := by rw [hD2]
    _ = Per 11 := h11.symm

end Omega.Conclusion
