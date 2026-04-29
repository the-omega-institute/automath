import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-maxfiber-loss-vs-fourmode-carrier`. -/
theorem paper_conclusion_maxfiber_loss_vs_fourmode_carrier {D carrierDim : ℕ} {loss : ℝ}
    (hD : 0 < D) (hLoss : loss = Real.log D) (hCarrier : carrierDim = 4) :
    loss = Real.log D ∧ carrierDim = 4 := by
  have _hD : 0 < D := hD
  exact ⟨hLoss, hCarrier⟩

end Omega.Conclusion
