import Mathlib.Tactic

namespace Omega.Conclusion

theorem paper_conclusion_resonance_window_unified_dyadic_shell_extremal_endpoint
    (a b : ℕ → ℕ)
    (hvals :
      a 9 = 3 ∧ b 9 = 4 ∧ a 10 = 5 ∧ b 10 = 4 ∧ a 11 = 3 ∧ b 11 = 6 ∧ a 12 = 7 ∧
        b 12 = 6 ∧ a 13 = 3 ∧ b 13 = 8 ∧ a 14 = 7 ∧ b 14 = 6 ∧ a 15 = 3 ∧ b 15 = 8 ∧
        a 16 = 7 ∧ b 16 = 6 ∧ a 17 = 3 ∧ b 17 = 10) :
    (∀ q, 9 ≤ q → q ≤ 17 → a q ≤ 7 ∧ b q ≤ 10) ∧
      (∀ q, 9 ≤ q → q ≤ 17 → b q = 10 → q = 17) := by
  rcases hvals with
    ⟨ha9, hb9, ha10, hb10, ha11, hb11, ha12, hb12, ha13, hb13, ha14, hb14, ha15, hb15, ha16,
      hb16, ha17, hb17⟩
  refine ⟨?_, ?_⟩
  · intro q hq9 hq17
    interval_cases q <;> constructor <;> omega
  · intro q hq9 hq17 hq
    interval_cases q <;> simp [hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17] at hq ⊢

end Omega.Conclusion
