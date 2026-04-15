import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Basic

namespace Omega.EA

/-- Fibonacci valuation Val_pr.
    def:prime-register-fib-valuation-zg-code -/
noncomputable def valPr (a : ℕ →₀ ℕ) : ℕ :=
  a.sum (fun k n => n * Nat.fib (k + 2))

/-- valPr of zero is zero.
    def:prime-register-fib-valuation-zg-code -/
theorem valPr_zero : valPr 0 = 0 := by
  unfold valPr
  simp

/-- valPr on a single basis element.
    def:prime-register-fib-valuation-zg-code -/
theorem valPr_single (k n : ℕ) :
    valPr (Finsupp.single k n) = n * Nat.fib (k + 2) := by
  unfold valPr
  rw [Finsupp.sum_single_index]
  simp

/-- valPr is additive.
    def:prime-register-fib-valuation-zg-code -/
theorem valPr_add (a b : ℕ →₀ ℕ) :
    valPr (a + b) = valPr a + valPr b := by
  unfold valPr
  rw [Finsupp.sum_add_index']
  · intro i; simp
  · intros i m n; ring

/-- Paper definition realisation: zero, single, additivity, and small-value witnesses.
    def:prime-register-fib-valuation-zg-code -/
theorem paper_prime_register_fib_valuation_def :
    valPr 0 = 0 ∧
    (∀ (k n : ℕ), valPr (Finsupp.single k n) = n * Nat.fib (k + 2)) ∧
    (∀ (a b : ℕ →₀ ℕ), valPr (a + b) = valPr a + valPr b) ∧
    (∀ (k : ℕ), valPr (Finsupp.single k 1) = Nat.fib (k + 2)) ∧
    (valPr (Finsupp.single 0 1) = 1) ∧
    (valPr (Finsupp.single 1 1) = 2) ∧
    (valPr (Finsupp.single 2 1) = 3) := by
  refine ⟨valPr_zero, valPr_single, valPr_add, ?_, ?_, ?_, ?_⟩
  · intro k; rw [valPr_single]; ring
  · rw [valPr_single]; decide
  · rw [valPr_single]; decide
  · rw [valPr_single]; decide

end Omega.EA
