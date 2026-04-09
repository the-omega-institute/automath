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

end Omega.Conclusion.ReversibleAuxBitsBudget
