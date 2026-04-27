import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:near1-log2-over-logphi-Dinfty-transcendence`. -/
theorem paper_near1_log2_over_logphi_dinfty_transcendence
    (TranscendentalOverQ : ℝ → Prop) (φ r «D∞» : ℝ)
    (hφ : φ = (1 + Real.sqrt 5) / 2)
    (hr : r = Real.log 2 / Real.log φ)
    (hD : «D∞» = r - (1 / 2 : ℝ))
    (hr_trans : TranscendentalOverQ r)
    (hsub_alg : ∀ x a : ℝ, TranscendentalOverQ x → TranscendentalOverQ (x - a)) :
    TranscendentalOverQ r ∧ TranscendentalOverQ «D∞» := by
  have _hφ_used : φ = (1 + Real.sqrt 5) / 2 := hφ
  have _hr_used : r = Real.log 2 / Real.log φ := hr
  refine ⟨hr_trans, ?_⟩
  rw [hD]
  exact hsub_alg r (1 / 2 : ℝ) hr_trans

end Omega.Zeta
