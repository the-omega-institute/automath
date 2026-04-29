import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Folding.FiberWeightCount

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-even-maxfiber-hiddenbit-exact-fairization`. -/
theorem paper_conclusion_window6_even_maxfiber_hiddenbit_exact_fairization
    (k : ℕ) (x₁ x₂ : Omega.X (2 * k)) :
    Omega.fiberHiddenBitCount 0 x₁ = Nat.fib (k + 1) →
      Omega.fiberHiddenBitCount 1 x₁ = Nat.fib k →
      Omega.fiberHiddenBitCount 0 x₂ = Nat.fib k →
      Omega.fiberHiddenBitCount 1 x₂ = Nat.fib (k + 1) →
      ((Omega.fiberHiddenBitCount 1 x₁ : ℝ) / Nat.fib (k + 2) = (Nat.fib k : ℝ) / Nat.fib (k + 2)) ∧
        ((Omega.fiberHiddenBitCount 1 x₂ : ℝ) / Nat.fib (k + 2) =
            (Nat.fib (k + 1) : ℝ) / Nat.fib (k + 2)) ∧
        (((Omega.fiberHiddenBitCount 1 x₁ : ℝ) / Nat.fib (k + 2) +
              (Omega.fiberHiddenBitCount 1 x₂ : ℝ) / Nat.fib (k + 2)) / 2 =
            (1 / 2 : ℝ)) := by
  intro h₀₁ h₁₁ h₀₂ h₁₂
  have hfib_pos : 0 < Nat.fib (k + 2) := by
    exact Nat.fib_pos.2 (by omega)
  have hden_ne : (Nat.fib (k + 2) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hfib_pos
  have hfib : Nat.fib (k + 2) = Nat.fib (k + 1) + Nat.fib k := by
    simpa [add_comm] using (Nat.fib_add_two (n := k))
  have hone_sum :
      Omega.fiberHiddenBitCount 1 x₁ + Omega.fiberHiddenBitCount 1 x₂ = Nat.fib (k + 2) :=
    by omega
  have hone_sum' :
      ((Omega.fiberHiddenBitCount 1 x₁ + Omega.fiberHiddenBitCount 1 x₂ : Nat) : ℝ) =
        Nat.fib (k + 2) := by
    exact_mod_cast hone_sum
  refine ⟨by simp [h₁₁], by simp [h₁₂], ?_⟩
  have hsum :
      (Omega.fiberHiddenBitCount 1 x₁ : ℝ) / Nat.fib (k + 2) +
          (Omega.fiberHiddenBitCount 1 x₂ : ℝ) / Nat.fib (k + 2) =
        1 := by
    calc
      (Omega.fiberHiddenBitCount 1 x₁ : ℝ) / Nat.fib (k + 2) +
          (Omega.fiberHiddenBitCount 1 x₂ : ℝ) / Nat.fib (k + 2) =
          (((Omega.fiberHiddenBitCount 1 x₁ : ℝ) + Omega.fiberHiddenBitCount 1 x₂) /
            Nat.fib (k + 2)) := by rw [← add_div]
      _ = (((Omega.fiberHiddenBitCount 1 x₁ + Omega.fiberHiddenBitCount 1 x₂ : Nat) : ℝ) /
            Nat.fib (k + 2)) := by norm_num
      _ = 1 := by
        rw [hone_sum']
        field_simp [hden_ne]
  calc
    ((Omega.fiberHiddenBitCount 1 x₁ : ℝ) / Nat.fib (k + 2) +
          (Omega.fiberHiddenBitCount 1 x₂ : ℝ) / Nat.fib (k + 2)) /
        2 =
        (1 : ℝ) / 2 := by rw [hsum]
    _ = (1 / 2 : ℝ) := by ring

end Omega.Conclusion
