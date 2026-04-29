import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-gauge-anomaly-no-three-mode-emulator`. -/
theorem paper_conclusion_gauge_anomaly_no_three_mode_emulator (Candidate : Type*)
    (carrierDim : Candidate → ℕ) (passesTimeCertificate passesFrequencyCertificate : Candidate → Prop)
    (hmin :
      ∀ c, passesTimeCertificate c → passesFrequencyCertificate c → 4 ≤ carrierDim c) :
    ∀ c, carrierDim c < 4 → ¬ (passesTimeCertificate c ∧ passesFrequencyCertificate c) := by
  intro c hdim hcert
  exact (not_le_of_gt hdim) (hmin c hcert.1 hcert.2)

end Omega.Conclusion
