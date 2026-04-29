import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-anomaly-certificate-linear-incompressibility`. -/
theorem paper_conclusion_anomaly_certificate_linear_incompressibility
    (q : ℕ) (A α s : ℝ) (hα : 0 < α) (hcert : (q : ℝ) * A ≤ α * s) :
    (q : ℝ) * A / α ≤ s := by
  rw [div_le_iff₀ hα]
  nlinarith

end Omega.Conclusion
