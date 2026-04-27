import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-window6-coherence-depth-v2`. -/
theorem paper_conclusion_window6_coherence_depth_v2 (n k : ℕ) :
    (8 ^ k ∣ n ↔ 2 ^ (3 * k) ∣ n) ∧ 8 ^ k = 2 ^ (3 * k) := by
  have hpow : 8 ^ k = 2 ^ (3 * k) := by
    calc
      8 ^ k = ((2 : ℕ) ^ 3) ^ k := by norm_num
      _ = 2 ^ (3 * k) := by rw [pow_mul]
  exact ⟨by rw [hpow], hpow⟩

end Omega.Conclusion
