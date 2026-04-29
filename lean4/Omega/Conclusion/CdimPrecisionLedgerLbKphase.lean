import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-cdim-precision-ledger-lb-kphase`. -/
theorem paper_conclusion_cdim_precision_ledger_lb_kphase {α : Type*} (φ : α → α)
    (d : α → α → ℝ) (ε B : ℝ) (hsep : ∀ x y, x ≠ y → ε ≤ d (φ x) (φ y))
    (hcrowd : ∃ x y, x ≠ y ∧ d (φ x) (φ y) ≤ B) :
    ε ≤ B := by
  rcases hcrowd with ⟨x, y, hxy, hdist⟩
  exact le_trans (hsep x y hxy) hdist

end Omega.Conclusion
