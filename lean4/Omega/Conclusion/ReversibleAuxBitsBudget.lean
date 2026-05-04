import Mathlib.Tactic

/-!
# Reversible auxiliary bits budget

The reversible auxiliary bit exponent κ(π) = ⌈log₂ b(π)⌉ where b(π)
is the minimum external budget. We verify seed values for Nat.clog 2
and the encoding/tightness bounds.
-/

namespace Omega.Conclusion.ReversibleAuxBitsBudget

/-- Seed values for ⌈log₂ b⌉ and encoding bounds.
    prop:conclusion-reversible-aux-bits-equals-log-budget -/
theorem paper_conclusion_reversible_aux_bits_log_budget :
    Nat.clog 2 1 = 0 ∧ Nat.clog 2 2 = 1 ∧
    Nat.clog 2 3 = 2 ∧ Nat.clog 2 4 = 2 ∧
    Nat.clog 2 5 = 3 ∧ Nat.clog 2 8 = 3 ∧
    2 ^ Nat.clog 2 3 ≥ 3 ∧ 2 ^ Nat.clog 2 5 ≥ 5 := by
  refine ⟨by native_decide, by native_decide, by native_decide,
          by native_decide, by native_decide, by native_decide,
          by native_decide, by native_decide⟩

/-- The injection exists iff b ≤ 2^k: for b ≤ 2^k there is an injection
    Fin b → Fin (2^k).
    prop:conclusion-reversible-aux-bits-equals-log-budget -/
theorem injection_exists_iff (b k : ℕ) :
    (∃ f : Fin b → Fin (2 ^ k), Function.Injective f) ↔ b ≤ 2 ^ k := by
  constructor
  · rintro ⟨f, hf⟩
    have := Fintype.card_le_of_injective f hf
    simp [Fintype.card_fin] at this
    exact this
  · intro h
    exact ⟨Fin.castLE (by omega), Fin.castLE_injective (by omega)⟩

/-- Tightness: reducing k by 1 does not suffice for non-power-of-2 budgets.
    prop:conclusion-reversible-aux-bits-equals-log-budget -/
theorem clog_tightness_budget :
    ¬(3 ≤ 2 ^ (Nat.clog 2 3 - 1)) ∧
    ¬(5 ≤ 2 ^ (Nat.clog 2 5 - 1)) := by
  refine ⟨by native_decide, by native_decide⟩

-- Phase R610: clog monotonicity and Fibonacci budget seeds
-- ══════════════════════════════════════════════════════════════

/-- clog₂ is monotone.
    prop:conclusion-reversible-aux-bits-equals-log-budget -/
theorem clog2_mono {a b : ℕ} (h : a ≤ b) : Nat.clog 2 a ≤ Nat.clog 2 b :=
  Nat.clog_mono_right 2 h

/-- b ≤ 2^⌈log₂ b⌉.
    prop:conclusion-reversible-aux-bits-equals-log-budget -/
theorem pow_clog2_ge (b : ℕ) (_hb : 0 < b) : b ≤ 2 ^ Nat.clog 2 b :=
  Nat.le_pow_clog (by omega) b

/-- Paper-facing monotonicity and encoding package for reversible auxiliary budgets.
    prop:conclusion-reversible-aux-bits-equals-log-budget -/
theorem paper_conclusion_reversible_budget_monotone_package {a b : ℕ}
    (h : a ≤ b) (hb : 0 < b) :
    Nat.clog 2 a ≤ Nat.clog 2 b ∧ b ≤ 2 ^ Nat.clog 2 b := by
  exact ⟨clog2_mono h, pow_clog2_ge b hb⟩

/-- Extended clog₂ seed values.
    prop:conclusion-reversible-aux-bits-equals-log-budget -/
theorem clog2_extended_seeds :
    Nat.clog 2 1 = 0 ∧ Nat.clog 2 2 = 1 ∧ Nat.clog 2 3 = 2 ∧
    Nat.clog 2 4 = 2 ∧ Nat.clog 2 5 = 3 ∧ Nat.clog 2 8 = 3 ∧
    Nat.clog 2 9 = 4 ∧ Nat.clog 2 16 = 4 ∧ Nat.clog 2 21 = 5 ∧
    Nat.clog 2 34 = 6 ∧ Nat.clog 2 55 = 6 := by
  refine ⟨by native_decide, by native_decide, by native_decide,
          by native_decide, by native_decide, by native_decide,
          by native_decide, by native_decide, by native_decide,
          by native_decide, by native_decide⟩

/-- Paper package: clog₂ of Fibonacci numbers.
    prop:conclusion-reversible-aux-bits-equals-log-budget -/
theorem paper_reversible_budget_extended :
    (Nat.clog 2 (Nat.fib 4) = 2) ∧ (Nat.clog 2 (Nat.fib 5) = 3) ∧
    (Nat.clog 2 (Nat.fib 6) = 3) ∧ (Nat.clog 2 (Nat.fib 7) = 4) ∧
    (Nat.clog 2 (Nat.fib 8) = 5) ∧ (Nat.clog 2 (Nat.fib 9) = 6) ∧
    (Nat.clog 2 (Nat.fib 10) = 6) := by
  refine ⟨by native_decide, by native_decide, by native_decide,
          by native_decide, by native_decide, by native_decide,
          by native_decide⟩

/-- Paper package: reversible auxiliary-bit budget via finite injective encodings.
    This packages the finite-state encoding criterion as an iff statement.
    prop:conclusion-reversible-aux-bits-equals-log-budget -/
theorem paper_conclusion_reversible_aux_bits_log_budget_package (b k : ℕ) :
    (∃ f : Fin b → Fin (2 ^ k), Function.Injective f) ↔ b ≤ 2 ^ k :=
  injection_exists_iff b k

/-- Exact reversible auxiliary-bit budget: `Nat.clog 2 b` is the least exponent whose
    binary address space has size at least `b`.
    prop:conclusion-reversible-aux-bits-equals-log-budget -/
theorem paper_conclusion_reversible_aux_bits_equals_log_budget (b : ℕ) (hb : 0 < b) :
    b ≤ 2 ^ Nat.clog 2 b ∧ ∀ k : ℕ, b ≤ 2 ^ k → Nat.clog 2 b ≤ k := by
  exact ⟨pow_clog2_ge b hb, fun _ h => Nat.clog_le_of_le_pow h⟩

end Omega.Conclusion.ReversibleAuxBitsBudget
