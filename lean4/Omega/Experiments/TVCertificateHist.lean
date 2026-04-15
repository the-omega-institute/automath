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

/-- Paper-facing Parry-baseline decomposition: the finite-sample folded-histogram certificate
is combined with one triangle-inequality step to separate the empirical error from the
structural gap to the Parry reference measure.
    cor:tv-decomposition-parry -/
theorem paper_tv_decomposition_parry
    (m : ℕ) (tvMicro tvFold tvParry gap star : ℝ)
    (hMicro : tvMicro ≤ (m + 1 : ℝ) * star) (hFold : tvFold ≤ tvMicro)
    (hTriangle : tvParry ≤ tvFold + gap) :
    tvMicro ≤ (m + 1 : ℝ) * star ∧
      tvFold ≤ (m + 1 : ℝ) * star ∧
      tvParry ≤ (m + 1 : ℝ) * star + gap := by
  obtain ⟨hMicro', hFold'⟩ := paper_tv_certificate_hist m tvMicro tvFold star hMicro hFold
  refine ⟨hMicro', hFold', ?_⟩
  linarith

end Omega.Experiments.TVCertificateHist
