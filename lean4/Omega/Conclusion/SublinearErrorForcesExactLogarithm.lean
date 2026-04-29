import Omega.Conclusion.LogRigidityUnderTropical

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-sublinear-error-forces-exact-logarithm`. -/
theorem paper_conclusion_sublinear_error_forces_exact_logarithm (δ : ℕ → ℝ) (c : ℝ)
    (Sublinear : Prop) (hmul : MultiplicativeOnPos δ)
    (hGlobalSub : (∀ n : ℕ, 1 ≤ n → δ n = c * Real.log n) → Sublinear)
    (hSubPrime : Sublinear → ∀ p : ℕ, Nat.Prime p → δ p = c * Real.log p)
    (hPrimeGlobal :
      (∀ p : ℕ, Nat.Prime p → δ p = c * Real.log p) →
        ∀ n : ℕ, 1 ≤ n → δ n = c * Real.log n) :
    (Sublinear ↔ (∀ p : ℕ, Nat.Prime p → δ p = c * Real.log p)) ∧
      ((∀ p : ℕ, Nat.Prime p → δ p = c * Real.log p) ↔
        ∀ n : ℕ, 1 ≤ n → δ n = c * Real.log n) := by
  have _hmul : MultiplicativeOnPos δ := hmul
  refine ⟨?_, ?_⟩
  · refine ⟨hSubPrime, ?_⟩
    intro hPrime
    exact hGlobalSub (hPrimeGlobal hPrime)
  · refine ⟨hPrimeGlobal, ?_⟩
    intro hGlobal p hp
    exact hGlobal p hp.one_le

end Omega.Conclusion
