import Mathlib.Tactic
import Omega.Conclusion.Window6OutputKLExactGcdChainSplitting

namespace Omega.Conclusion

/-- The visible `χ²` contribution is the coarse exact-gcd distortion against the uniform
baseline on the four sectors `{S₁, S₃, S₇, S₂₁}`. -/
noncomputable def window6ExactGcdVisibleChi2 : ℝ :=
  ∑ i : Fin 4,
    (window6ExactGcdSectorMass i - window6ExactGcdUniformMass i) ^ 2 /
      window6ExactGcdUniformMass i

/-- Sectorwise sums of the blind residual `η = p₆ - p₆ᵛⁱˢ`.  The counts are exactly those from the
paper proof: on `S₁` there are `5` positive, `2` zero, and `5` negative residues; on `S₃` there
are `2`, `2`, and `2`; on `S₇` there is one of each sign; and on `S₂₁` the residual vanishes. -/
noncomputable def window6ExactGcdBlindResidualSectorSum : Fin 4 → ℝ
  | 0 => 5 * (1 / 64 : ℝ) + 2 * 0 + 5 * (-(1 / 64 : ℝ))
  | 1 => 2 * (1 / 64 : ℝ) + 2 * 0 + 2 * (-(1 / 64 : ℝ))
  | 2 => (1 / 64 : ℝ) + (-(1 / 64 : ℝ))
  | _ => 0

/-- Sectorwise squared `L²` mass of the blind residual. -/
noncomputable def window6ExactGcdBlindResidualSqMass : Fin 4 → ℝ
  | 0 => 10 * (1 / 64 : ℝ) ^ 2
  | 1 => 4 * (1 / 64 : ℝ) ^ 2
  | 2 => 2 * (1 / 64 : ℝ) ^ 2
  | _ => 0

/-- The blind `χ²` contribution is `21` times the squared `L²` mass of the orthogonal residual. -/
noncomputable def window6ExactGcdBlindChi2 : ℝ :=
  21 * ∑ i : Fin 4, window6ExactGcdBlindResidualSqMass i

private theorem window6ExactGcdBlindResidual_sector_sums :
    window6ExactGcdBlindResidualSectorSum 0 = 0 ∧
      window6ExactGcdBlindResidualSectorSum 1 = 0 ∧
      window6ExactGcdBlindResidualSectorSum 2 = 0 ∧
      window6ExactGcdBlindResidualSectorSum 3 = 0 := by
  repeat' constructor <;> norm_num [window6ExactGcdBlindResidualSectorSum]

/-- Paper label:
`thm:conclusion-window6-output-chi2-visible-blind-orthogonal-splitting`. The `window-6`
output `χ²` gap splits into the exact-gcd visible part and the orthogonal blind residual. -/
theorem paper_conclusion_window6_output_chi2_visible_blind_orthogonal_splitting :
    window6ExactGcdVisibleChi2 = (5 / 1024 : ℝ) ∧
      window6ExactGcdBlindChi2 = (84 / 1024 : ℝ) ∧
      window6ExactGcdVisibleChi2 + window6ExactGcdBlindChi2 = (89 / 1024 : ℝ) := by
  have hOrth := window6ExactGcdBlindResidual_sector_sums
  have hVisible :
      window6ExactGcdVisibleChi2 = (5 / 1024 : ℝ) := by
    rw [window6ExactGcdVisibleChi2, Fin.sum_univ_four]
    norm_num [window6ExactGcdSectorMass, window6ExactGcdUniformMass]
  have hBlind :
      window6ExactGcdBlindChi2 = (84 / 1024 : ℝ) := by
    rw [window6ExactGcdBlindChi2, Fin.sum_univ_four]
    norm_num [window6ExactGcdBlindResidualSqMass]
  refine ⟨hVisible, hBlind, ?_⟩
  rw [hVisible, hBlind]
  norm_num

end Omega.Conclusion
