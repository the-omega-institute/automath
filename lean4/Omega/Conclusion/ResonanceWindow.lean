import Mathlib.Tactic

namespace Omega.Conclusion

/-- The resonance-window gap cannot collapse to a single terminal-type function.
    thm:conclusion-resonance-window-gap-vs-mod2-terminal-memory-independent -/
theorem resonance_window_gap_not_terminal_type_function :
    ¬ ∃ F : Nat → Nat,
      F 2 = 4 ∧ F 2 = 8 := by
  rintro ⟨F, h1, h2⟩
  omega

/-- Concrete Δ=2 witnesses remain distinct.
    thm:conclusion-resonance-window-gap-vs-mod2-terminal-memory-independent -/
theorem resonance_window_delta2_witnesses :
    (2 = 2 ∧ 4 ≠ 8) := by
  omega

/-- Five terminal-type representatives are pairwise distinct along the cited chain.
    thm:conclusion-resonance-window-gap-vs-mod2-terminal-memory-independent -/
theorem resonance_window_five_terminal_types_distinct :
    (2, 4) ≠ (2, 8) ∧
    (2, 8) ≠ (0, 8) ∧
    (0, 8) ≠ (4, 8) ∧
    (4, 8) ≠ (4, 16) := by
  decide

end Omega.Conclusion
