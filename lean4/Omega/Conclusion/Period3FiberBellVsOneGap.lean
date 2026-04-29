import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-period3-fiber-bell-vs-one-gap`. -/
theorem paper_conclusion_period3_fiber_bell_vs_one_gap
    (Bell : ℕ → ℕ)
    (hBellLower : ∀ n : ℕ, 1 ≤ n → 2 ^ (n - 1) ≤ Bell n) :
    (∀ B : ℕ, ∃ n : ℕ, B ≤ Bell (2 ^ n) / 2) ∧
      (∀ B : ℕ, ∃ n : ℕ, B ≤ Nat.factorial (2 ^ n - 1) / 2) := by
  constructor
  · intro B
    refine ⟨B + 3, ?_⟩
    have hExpLarge : B ≤ 2 ^ (B + 3) - 1 := by
      have hpow : 2 * (B + 3) ≤ 2 ^ (B + 3) :=
        Nat.mul_le_pow (by norm_num) (B + 3)
      omega
    have hPowB : 2 * B ≤ 2 ^ B := Nat.mul_le_pow (by norm_num) B
    have hMono : 2 ^ B ≤ 2 ^ (2 ^ (B + 3) - 1) :=
      pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2) hExpLarge
    have hBell : 2 ^ (2 ^ (B + 3) - 1) ≤ Bell (2 ^ (B + 3)) :=
      hBellLower (2 ^ (B + 3)) (by
        have : 0 < 2 ^ (B + 3) := pow_pos (by norm_num) _
        omega)
    have hTwoB : 2 * B ≤ Bell (2 ^ (B + 3)) := hPowB.trans (hMono.trans hBell)
    have hDiv : 2 * B / 2 ≤ Bell (2 ^ (B + 3)) / 2 := Nat.div_le_div_right hTwoB
    rw [Nat.mul_div_right B (by norm_num : 0 < 2)] at hDiv
    exact hDiv
  · intro B
    refine ⟨B + 2, ?_⟩
    have hArgLarge : 2 * B ≤ 2 ^ (B + 2) - 1 := by
      have hpow : 2 * (B + 2) ≤ 2 ^ (B + 2) :=
        Nat.mul_le_pow (by norm_num) (B + 2)
      omega
    have hFact : 2 ^ (B + 2) - 1 ≤ Nat.factorial (2 ^ (B + 2) - 1) :=
      Nat.self_le_factorial (2 ^ (B + 2) - 1)
    have hTwoB : 2 * B ≤ Nat.factorial (2 ^ (B + 2) - 1) := hArgLarge.trans hFact
    have hDiv : 2 * B / 2 ≤ Nat.factorial (2 ^ (B + 2) - 1) / 2 :=
      Nat.div_le_div_right hTwoB
    rw [Nat.mul_div_right B (by norm_num : 0 < 2)] at hDiv
    exact hDiv

end Omega.Conclusion
