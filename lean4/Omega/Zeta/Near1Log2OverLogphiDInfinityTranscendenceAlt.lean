import Omega.Zeta.Near1Log2OverLogphiDInfinityTranscendence

namespace Omega.Zeta

/-- Paper label: `prop:near1-log2-over-logphi-Dinfty-transcendence-alt`. -/
theorem paper_near1_log2_over_logphi_dinfty_transcendence_alt
    (TranscendentalOverQ : ℝ → Prop) (φ r «D∞» : ℝ)
    (hφ : φ = (1 + Real.sqrt 5) / 2)
    (hr : r = Real.log 2 / Real.log φ)
    (hD : «D∞» = r - (1 / 2 : ℝ))
    (hr_trans : TranscendentalOverQ r)
    (hsub_alg : ∀ x a : ℝ, TranscendentalOverQ x → TranscendentalOverQ (x - a)) :
    TranscendentalOverQ r ∧ TranscendentalOverQ «D∞» := by
  exact
    paper_near1_log2_over_logphi_dinfty_transcendence TranscendentalOverQ φ r «D∞» hφ hr
      hD hr_trans hsub_alg

end Omega.Zeta
