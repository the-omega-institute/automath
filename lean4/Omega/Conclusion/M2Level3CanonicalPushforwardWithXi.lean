import Mathlib.Tactic
import Omega.Conclusion.M2Level3XiRamificationPushforward

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-m2-level3-canonical-pushforward-with-xi`. The ramification
pushforward coefficients from the `Ξ`-cover audit combine with
`K_{\overline{\mathcal M}_2} ≡ -(11/5) Δ₀ + (6/5) Δ₁` by a direct projection-formula
computation on the Klingen, Siegel, and flag covers. -/
theorem paper_conclusion_m2_level3_canonical_pushforward_with_xi :
    conclusion_m2_level3_xi_ramification_pushforward_klingen = (18, 0, 16) ∧
      conclusion_m2_level3_xi_ramification_pushforward_siegel = (24, 0, 12) ∧
      conclusion_m2_level3_xi_ramification_pushforward_flag = (96, 0, 64) ∧
      (((-70 : ℚ), (48 : ℚ), (16 : ℚ)) = ((40 : ℚ) * ((-11 : ℚ) / 5) + 18,
        (40 : ℚ) * ((6 : ℚ) / 5), 16)) ∧
      (((-64 : ℚ), (48 : ℚ), (12 : ℚ)) = ((40 : ℚ) * ((-11 : ℚ) / 5) + 24,
        (40 : ℚ) * ((6 : ℚ) / 5), 12)) ∧
      (((-256 : ℚ), (192 : ℚ), (64 : ℚ)) = ((160 : ℚ) * ((-11 : ℚ) / 5) + 96,
        (160 : ℚ) * ((6 : ℚ) / 5), 64)) := by
  rcases paper_conclusion_m2_level3_xi_ramification_pushforward with ⟨hKl, hSi, hFl⟩
  refine ⟨hKl, ⟨hSi, ⟨hFl, ⟨?_, ⟨?_, ?_⟩⟩⟩⟩⟩
  all_goals
    norm_num

end Omega.Conclusion
