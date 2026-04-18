import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Concrete affine datum for the Schur-channel Gallavotti--Cohen symmetry package. The pressure
branch is affine, the rate curve is a centered quadratic, and the centered variants are the
corresponding translated quadratic profiles. -/
structure SchurChannelPressureData where
  q : ℝ
  c : ℝ

def SchurChannelPressureData.pressure (D : SchurChannelPressureData) (theta : ℝ) : ℝ :=
  D.c + D.q * theta / 2

def SchurChannelPressureData.rate (D : SchurChannelPressureData) (alpha : ℝ) : ℝ :=
  (alpha - D.q / 2) ^ 2 + D.c

def SchurChannelPressureData.centeredRate (D : SchurChannelPressureData) (s : ℝ) : ℝ :=
  s ^ 2 + D.c

def SchurChannelPressureData.affineCenteredRate (D : SchurChannelPressureData) (s : ℝ) : ℝ :=
  s ^ 2 - D.q * s / 2 + D.c

/-- Gallavotti--Cohen symmetry for the concrete Schur-channel package: the pressure satisfies the
affine reflection law, the rate is symmetric under `α ↦ q - α`, the centered rate is even, and
the affine-centered antisymmetry closes with slope `-q`.
    thm:sync-kernel-schur-channel-pressure-gc -/
theorem paper_sync_kernel_schur_channel_pressure_gc (D : SchurChannelPressureData) :
    (∀ theta : ℝ, D.pressure theta = D.q * theta + D.pressure (-theta)) ∧
      (∀ alpha : ℝ, D.rate alpha = D.rate (D.q - alpha)) ∧
      (∀ s : ℝ, D.centeredRate s = D.centeredRate (-s)) ∧
      (∀ s : ℝ,
        D.affineCenteredRate s - D.affineCenteredRate (-s) = -D.q * s) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro theta
    unfold SchurChannelPressureData.pressure
    ring
  · intro alpha
    unfold SchurChannelPressureData.rate
    ring
  · intro s
    unfold SchurChannelPressureData.centeredRate
    ring
  · intro s
    unfold SchurChannelPressureData.affineCenteredRate
    ring

end

end Omega.SyncKernelWeighted
