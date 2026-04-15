import Mathlib.Tactic

namespace Omega.Experiments.TVCertificateHist

/-- Paper-facing bridge from the microstate discrepancy certificate to the folded histogram
certificate: the microstate total-variation bound propagates unchanged to the folded histogram
once total variation is monotone under pushforward.
    thm:tv-certificate-hist -/
theorem paper_tv_certificate_hist
    (m : ℕ) (tvMicro tvFold star : ℝ)
    (hMicro : tvMicro ≤ (m + 1 : ℝ) * star) (hFold : tvFold ≤ tvMicro) :
    tvMicro ≤ (m + 1 : ℝ) * star ∧ tvFold ≤ (m + 1 : ℝ) * star := by
  refine ⟨hMicro, le_trans hFold hMicro⟩

end Omega.Experiments.TVCertificateHist
