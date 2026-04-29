import Mathlib.Tactic
import Omega.Conclusion.Window6OutputChi2VisibleBlindOrthogonalSplitting
import Omega.Conclusion.Window6OutputKLExactGcdChainSplitting

namespace Omega.Conclusion

/-- Paper label:
`cor:conclusion-window6-output-blind-channel-dominates`. In the audited window-`6` split, the
blind channel carries the dominant share of both the `χ²` distortion and the KL divergence. -/
theorem paper_conclusion_window6_output_blind_channel_dominates :
    window6ExactGcdBlindChi2 / (window6ExactGcdVisibleChi2 + window6ExactGcdBlindChi2) =
        (84 / 89 : ℝ) ∧
      window6ExactGcdBlindKl / (window6ExactGcdVisibleKl + window6ExactGcdBlindKl) =
        ((1 / 4 : ℝ) * Real.log (32 / 27 : ℝ)) /
          ((15 / 16 : ℝ) * Real.log (63 / 64 : ℝ) +
            (1 / 16 : ℝ) * Real.log (21 / 16 : ℝ) +
            (1 / 4 : ℝ) * Real.log (32 / 27 : ℝ)) := by
  rcases paper_conclusion_window6_output_chi2_visible_blind_orthogonal_splitting with
    ⟨hVisibleChi2, hBlindChi2, _⟩
  rcases paper_conclusion_window6_output_kl_exact_gcd_chain_splitting with
    ⟨hVisibleKl, hBlindKl, _⟩
  refine ⟨?_, ?_⟩
  · rw [hBlindChi2, hVisibleChi2]
    norm_num
  · rw [hBlindKl, hVisibleKl]

end Omega.Conclusion
