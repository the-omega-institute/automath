import Mathlib.Tactic
import Omega.Conclusion.JensenDefectZeroStockIdentity

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-jensen-defect-entropy-saturation-exclusion`. The zero-stock
identity turns the energy gap into twice the zero-stock sum, so equality is exactly zero stock
and a gap bounded by `2ε` bounds the stock by `ε`. -/
theorem paper_conclusion_jensen_defect_entropy_saturation_exclusion
    (D : conclusion_jensen_defect_zero_stock_identity_data) :
    (D.zeroStockSum = 0 ↔ D.energyTerm = D.reverseKL) ∧
      (∀ ε : ℝ, 0 ≤ ε → D.energyTerm - D.reverseKL ≤ 2 * ε → D.zeroStockSum ≤ ε) := by
  rcases paper_conclusion_jensen_defect_zero_stock_identity D with ⟨_, hgap, _⟩
  refine ⟨?_, ?_⟩
  · constructor
    · intro hzero
      linarith
    · intro henergy
      linarith
  · intro ε _hε hbound
    linarith

end Omega.Conclusion
