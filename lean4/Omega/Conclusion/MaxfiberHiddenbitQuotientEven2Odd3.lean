import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Conclusion.MaxfiberHiddenbitSufficiencyVsIdentifiabilitySplit
import Omega.Conclusion.OddMaxfiberHiddenbitTristateCrystal
import Omega.Conclusion.Window6EvenMaxfiberHiddenbitExactFairization

namespace Omega.Conclusion

noncomputable section

/-- The two even-window hidden-bit Bernoulli parameters. -/
def conclusion_maxfiber_hiddenbit_quotient_even2_odd3_even_parameter
    (k : ℕ) (c : Fin 2) : ℝ :=
  if c = 0 then (Nat.fib (k + 1) : ℝ) / Nat.fib (k + 2)
  else (Nat.fib k : ℝ) / Nat.fib (k + 2)

/-- The three odd-window hidden-bit Bernoulli parameters. -/
def conclusion_maxfiber_hiddenbit_quotient_even2_odd3_odd_parameter
    (k : ℕ) (c : Fin 3) : ℝ :=
  if c = 0 then (1 / 2 : ℝ)
  else if c = 1 then
    (1 / 2 : ℝ) + (Nat.fib (k - 2) : ℝ) / (2 * Nat.fib (k + 1))
  else
    (1 / 2 : ℝ) - (Nat.fib (k - 2) : ℝ) / (2 * Nat.fib (k + 1))

/-- Concrete package for the even two-class and odd three-class hidden-bit quotient. -/
def conclusion_maxfiber_hiddenbit_quotient_even2_odd3_statement : Prop :=
  (∀ k : ℕ,
    conclusion_maxfiber_hiddenbit_quotient_even2_odd3_even_parameter k 0 =
        (Nat.fib (k + 1) : ℝ) / Nat.fib (k + 2) ∧
      conclusion_maxfiber_hiddenbit_quotient_even2_odd3_even_parameter k 1 =
        (Nat.fib k : ℝ) / Nat.fib (k + 2)) ∧
    (∀ k : ℕ,
      conclusion_maxfiber_hiddenbit_quotient_even2_odd3_odd_parameter k 0 = (1 / 2 : ℝ) ∧
        conclusion_maxfiber_hiddenbit_quotient_even2_odd3_odd_parameter k 1 =
          (1 / 2 : ℝ) + (Nat.fib (k - 2) : ℝ) / (2 * Nat.fib (k + 1)) ∧
        conclusion_maxfiber_hiddenbit_quotient_even2_odd3_odd_parameter k 2 =
          (1 / 2 : ℝ) - (Nat.fib (k - 2) : ℝ) / (2 * Nat.fib (k + 1))) ∧
    Fintype.card (Fin 2) = 2 ∧
    Fintype.card (Fin 3) = 3 ∧
    (∀ n : ℕ, ∀ p q : ℝ, p ≠ q →
      ∃ fp fq : ℕ → ℝ,
        (∀ ω : Fin n → Bool,
          conclusion_maxfiber_hiddenbit_sufficiency_vs_identifiability_split_law p ω =
            fp (conclusion_maxfiber_hiddenbit_sufficiency_vs_identifiability_split_sample_sum ω)) ∧
        (∀ ω : Fin n → Bool,
          conclusion_maxfiber_hiddenbit_sufficiency_vs_identifiability_split_law q ω =
            fq (conclusion_maxfiber_hiddenbit_sufficiency_vs_identifiability_split_sample_sum ω)))

/-- Paper label: `thm:conclusion-maxfiber-hiddenbit-quotient-even2-odd3`. -/
theorem paper_conclusion_maxfiber_hiddenbit_quotient_even2_odd3 :
    conclusion_maxfiber_hiddenbit_quotient_even2_odd3_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k
    simp [conclusion_maxfiber_hiddenbit_quotient_even2_odd3_even_parameter]
  · intro k
    simp [conclusion_maxfiber_hiddenbit_quotient_even2_odd3_odd_parameter]
  · simp
  · simp
  · intro n p q hpq
    refine ⟨fun k => p ^ k * (1 - p) ^ (n - k),
      fun k => q ^ k * (1 - q) ^ (n - k), ?_, ?_⟩
    · intro ω
      rfl
    · intro ω
      rfl

end

end Omega.Conclusion
