import Omega.SyncKernelRealInput.GMAbsCenteredOddMomentExtremal
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

open scoped BigOperators

noncomputable section

/-- Concrete data for the three-channel centered odd-moment certificate. -/
structure gm_abs_centered_moment_three_channels_data where
  gm_abs_centered_moment_three_channels_m : Nat
  gm_abs_centered_moment_three_channels_k : Nat
  gm_abs_centered_moment_three_channels_mean : ℝ
  gm_abs_centered_moment_three_channels_delta : ℝ
  gm_abs_centered_moment_three_channels_rest :
    Fin (gm_abs_centered_moment_three_channels_m - 1) → ℝ
  gm_abs_centered_moment_three_channels_main_channel : ℝ
  gm_abs_centered_moment_three_channels_energy_channel : ℝ
  gm_abs_centered_moment_three_channels_residual_saving : ℝ
  gm_abs_centered_moment_three_channels_hm :
    2 ≤ gm_abs_centered_moment_three_channels_m
  gm_abs_centered_moment_three_channels_hdelta :
    0 ≤ gm_abs_centered_moment_three_channels_delta
  gm_abs_centered_moment_three_channels_hsum :
    ∑ i, gm_abs_centered_moment_three_channels_rest i =
      -gm_abs_centered_moment_three_channels_delta
  gm_abs_centered_moment_three_channels_hmain :
    0 ≤ gm_abs_centered_moment_three_channels_main_channel
  gm_abs_centered_moment_three_channels_henergy :
    0 ≤ gm_abs_centered_moment_three_channels_energy_channel
  gm_abs_centered_moment_three_channels_hsaving :
    0 ≤ gm_abs_centered_moment_three_channels_residual_saving

/-- The explicit nonnegative contribution attached to the uniform main channel. -/
def gm_abs_centered_moment_three_channels_main
    (D : gm_abs_centered_moment_three_channels_data) : ℝ :=
  D.gm_abs_centered_moment_three_channels_main_channel

/-- The explicit energy-coupled contribution after the residual spectral saving is inserted. -/
def gm_abs_centered_moment_three_channels_energy
    (D : gm_abs_centered_moment_three_channels_data) : ℝ :=
  D.gm_abs_centered_moment_three_channels_residual_saving *
    D.gm_abs_centered_moment_three_channels_energy_channel

/-- The absolute centered odd moment used by the extremal theorem. -/
def gm_abs_centered_moment_three_channels_abs_moment
    (D : gm_abs_centered_moment_three_channels_data) : ℝ :=
  gm_abs_centered_odd_moment_extremal_moment
    D.gm_abs_centered_moment_three_channels_delta
    D.gm_abs_centered_moment_three_channels_rest
    D.gm_abs_centered_moment_three_channels_k

/-- The sharp two-level lower envelope from the existing odd-moment extremal theorem. -/
def gm_abs_centered_moment_three_channels_extremal_envelope
    (D : gm_abs_centered_moment_three_channels_data) : ℝ :=
  (1 +
      1 /
        (((D.gm_abs_centered_moment_three_channels_m - 1 : Nat) : ℝ) ^
          (2 * D.gm_abs_centered_moment_three_channels_k))) *
    D.gm_abs_centered_moment_three_channels_delta ^
      (2 * D.gm_abs_centered_moment_three_channels_k + 1)

/-- Paper-facing statement for `prop:gm-abs-centered-moment-three-channels`. -/
def gm_abs_centered_moment_three_channels_statement
    (D : gm_abs_centered_moment_three_channels_data) : Prop :=
  0 ≤ gm_abs_centered_moment_three_channels_main D ∧
    0 ≤ gm_abs_centered_moment_three_channels_energy D ∧
      gm_abs_centered_moment_three_channels_extremal_envelope D ≤
        gm_abs_centered_moment_three_channels_abs_moment D +
          gm_abs_centered_moment_three_channels_main D +
            gm_abs_centered_moment_three_channels_energy D

/-- Paper label: `prop:gm-abs-centered-moment-three-channels`. -/
theorem paper_gm_abs_centered_moment_three_channels
    (D : gm_abs_centered_moment_three_channels_data) :
    gm_abs_centered_moment_three_channels_statement D := by
  have hExtremal :=
    (paper_gm_abs_centered_odd_moment_extremal
      D.gm_abs_centered_moment_three_channels_m
      D.gm_abs_centered_moment_three_channels_k
      D.gm_abs_centered_moment_three_channels_hm
      D.gm_abs_centered_moment_three_channels_mean
      D.gm_abs_centered_moment_three_channels_delta
      D.gm_abs_centered_moment_three_channels_rest
      D.gm_abs_centered_moment_three_channels_hdelta
      D.gm_abs_centered_moment_three_channels_hsum).2
  have hEnergy :
      0 ≤ gm_abs_centered_moment_three_channels_energy D := by
    dsimp [gm_abs_centered_moment_three_channels_energy]
    exact mul_nonneg
      D.gm_abs_centered_moment_three_channels_hsaving
      D.gm_abs_centered_moment_three_channels_henergy
  refine ⟨?_, hEnergy, ?_⟩
  · exact D.gm_abs_centered_moment_three_channels_hmain
  · dsimp [gm_abs_centered_moment_three_channels_extremal_envelope,
      gm_abs_centered_moment_three_channels_abs_moment,
      gm_abs_centered_moment_three_channels_main] at hExtremal ⊢
    nlinarith [D.gm_abs_centered_moment_three_channels_hmain, hEnergy, hExtremal]

end

end Omega.SyncKernelRealInput
