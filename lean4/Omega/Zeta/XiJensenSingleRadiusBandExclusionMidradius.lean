import Mathlib.Tactic
import Omega.Zeta.XiJensenSingleRadiusBandExclusion

namespace Omega.Zeta

/-- Paper label: `cor:xi-jensen-single-radius-band-exclusion-midradius`. -/
theorem paper_xi_jensen_single_radius_band_exclusion_midradius
    (T Delta Dzeta : Real) (hT : 1 <= T) (hDelta : 0 < Delta ∧ Delta <= 1 / 2)
    (hDzeta :
      Dzeta < Real.log ((1 + jensenBandRadius T Delta) / (2 * jensenBandRadius T Delta))) :
    noOffcriticalZeroInBand T Delta := by
  let R : ℝ := jensenBandRadius T Delta
  let rho : ℝ := (1 + R) / 2
  have hR_pos : 0 < R := by
    dsimp [R, jensenBandRadius]
    have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
    have hTsq : 0 < T ^ 2 := by positivity
    have hRatioPos : 0 < (T ^ 2 + (1 - Delta) ^ 2) / (T ^ 2 + (1 + Delta) ^ 2) := by
      positivity
    exact Real.sqrt_pos.2 hRatioPos
  have hR_lt_one : R < 1 := by
    have hDenPos : 0 < T ^ 2 + (1 + Delta) ^ 2 := by positivity
    have hRatioNonneg : 0 ≤ (T ^ 2 + (1 - Delta) ^ 2) / (T ^ 2 + (1 + Delta) ^ 2) := by
      positivity
    have hNumLtDen : T ^ 2 + (1 - Delta) ^ 2 < T ^ 2 + (1 + Delta) ^ 2 := by
      nlinarith [hDelta.1]
    have hRatioLtOne : (T ^ 2 + (1 - Delta) ^ 2) / (T ^ 2 + (1 + Delta) ^ 2) < 1 := by
      field_simp [hDenPos.ne']
      nlinarith
    have hR_nonneg : 0 ≤ R := by
      dsimp [R, jensenBandRadius]
      positivity
    have hRsq : R * R = (T ^ 2 + (1 - Delta) ^ 2) / (T ^ 2 + (1 + Delta) ^ 2) := by
      dsimp [R, jensenBandRadius]
      rw [← sq, Real.sq_sqrt hRatioNonneg]
    nlinarith
  have hrho : R < rho := by
    dsimp [rho]
    linarith
  have hratio : rho / R = (1 + R) / (2 * R) := by
    dsimp [rho]
    field_simp [hR_pos.ne']
  have hDzeta' : Dzeta < Real.log (rho / R) := by
    simpa [hratio, R] using hDzeta
  exact paper_xi_jensen_single_radius_band_exclusion T Delta rho Dzeta hT hDelta hrho hDzeta'

end Omega.Zeta
