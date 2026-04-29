import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-window6-critical-vs-emergent-oddprimes`. -/
theorem paper_conclusion_window6_critical_vs_emergent_oddprimes
    (kerDim : ℕ → ℕ)
    (hker : ∀ p, Nat.Prime p → 7 ≤ p → p ≠ 23 → kerDim p = 0)
    (h23 : kerDim 23 = 1) :
    (∀ p, Nat.Prime p → 7 ≤ p → (kerDim p ≠ 0 ↔ p = 23)) ∧
      Disjoint ({23} : Finset ℕ) ({571} : Finset ℕ) := by
  constructor
  · intro p hp h7
    constructor
    · intro hnonzero
      by_cases hp23 : p = 23
      · exact hp23
      · have hzero : kerDim p = 0 := hker p hp h7 hp23
        exact (hnonzero hzero).elim
    · intro hp23
      rw [hp23, h23]
      norm_num
  · simp

end Omega.Conclusion
