import Mathlib.Tactic

namespace Omega.Zeta

/-- Sum of the four mod-4 Fourier channel energies. -/
def xi_time_part9d_mod4_fourier_channel_energy_channelSum
    (channel0 channel1 channel2 channel3 : ℝ) : ℝ :=
  channel0 + channel1 + channel2 + channel3

/-- Concrete data for the mod-4 Fourier channel decomposition and the Jensen defect audit. -/
structure xi_time_part9d_mod4_fourier_channel_energy_data where
  r : ℝ
  totalEnergy : ℝ
  channel0 : ℝ
  channel1 : ℝ
  channel2 : ℝ
  channel3 : ℝ
  jensenDefect : ℝ
  reverseKL : ℝ
  h_totalEnergy_split :
    totalEnergy =
      xi_time_part9d_mod4_fourier_channel_energy_channelSum channel0 channel1 channel2 channel3
  h_reverseKL_fourier :
    reverseKL ≤
      ((1 + r) / (1 - r)) ^ 2 *
        xi_time_part9d_mod4_fourier_channel_energy_channelSum channel0 channel1 channel2 channel3
  h_jensen_reverseKL : jensenDefect ≤ (1 / 2 : ℝ) * reverseKL

/-- Paper label: `prop:xi-time-part9d-mod4-fourier-channel-energy`. -/
theorem paper_xi_time_part9d_mod4_fourier_channel_energy
    (D : xi_time_part9d_mod4_fourier_channel_energy_data) :
    D.totalEnergy = D.channel0 + D.channel1 + D.channel2 + D.channel3 ∧
      D.jensenDefect ≤
        (1 / 2) * ((1 + D.r) / (1 - D.r)) ^ 2 *
          (D.channel0 + D.channel1 + D.channel2 + D.channel3) := by
  have h_energy :
      D.totalEnergy = D.channel0 + D.channel1 + D.channel2 + D.channel3 := by
    simpa [xi_time_part9d_mod4_fourier_channel_energy_channelSum] using D.h_totalEnergy_split
  refine ⟨h_energy, ?_⟩
  have h_scaled :
      (1 / 2 : ℝ) * D.reverseKL ≤
        (1 / 2 : ℝ) *
          (((1 + D.r) / (1 - D.r)) ^ 2 *
            xi_time_part9d_mod4_fourier_channel_energy_channelSum
              D.channel0 D.channel1 D.channel2 D.channel3) :=
    mul_le_mul_of_nonneg_left D.h_reverseKL_fourier (by norm_num)
  calc
    D.jensenDefect ≤ (1 / 2 : ℝ) * D.reverseKL := D.h_jensen_reverseKL
    _ ≤
        (1 / 2 : ℝ) *
          (((1 + D.r) / (1 - D.r)) ^ 2 *
            xi_time_part9d_mod4_fourier_channel_energy_channelSum
              D.channel0 D.channel1 D.channel2 D.channel3) := h_scaled
    _ =
        (1 / 2) * ((1 + D.r) / (1 - D.r)) ^ 2 *
          (D.channel0 + D.channel1 + D.channel2 + D.channel3) := by
      simp [xi_time_part9d_mod4_fourier_channel_energy_channelSum]
      ring

end Omega.Zeta
