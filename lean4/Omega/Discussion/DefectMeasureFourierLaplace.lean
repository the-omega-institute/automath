import Mathlib

namespace Omega.Discussion

/-- The Fourier transform of a single shifted Poisson atom, restricted to the real part of the
oscillatory factor. -/
noncomputable def shiftedPoissonFourierAtom (γ δ ξ : ℝ) : ℝ :=
  4 * Real.pi * (δ / (1 + δ)) * Real.exp (-(1 + δ) * |ξ|) * Real.cos (γ * ξ)

/-- Poisson smoothing multiplies the Fourier side by the semigroup factor `e^{-t |ξ|}`. -/
noncomputable def shiftedPoissonSmoothedAtom (γ δ t ξ : ℝ) : ℝ :=
  Real.exp (-t * |ξ|) * shiftedPoissonFourierAtom γ δ ξ

/-- The renormalized Fourier-Laplace fingerprint obtained after pulling out the Poisson factor. -/
noncomputable def atomicFourierLaplaceFingerprint (γ δ t ξ s : ℝ) : ℝ :=
  Real.exp ((t + 1) * s) * shiftedPoissonSmoothedAtom γ δ t ξ

/-- Zero-frequency slice of the fingerprint. -/
noncomputable def zeroFrequencyFingerprint (δ s : ℝ) : ℝ :=
  4 * Real.pi * (δ / (1 + δ)) * Real.exp (-s * δ)

lemma shiftedPoissonSmoothedAtom_formula (γ δ t ξ : ℝ) :
    shiftedPoissonSmoothedAtom γ δ t ξ =
      4 * Real.pi * (δ / (1 + δ)) * Real.exp (-(t + 1 + δ) * |ξ|) * Real.cos (γ * ξ) := by
  unfold shiftedPoissonSmoothedAtom shiftedPoissonFourierAtom
  have hexp :
      Real.exp (-t * |ξ|) * Real.exp (-(1 + δ) * |ξ|) =
        Real.exp (-(t + 1 + δ) * |ξ|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    Real.exp (-t * |ξ|) *
        (4 * Real.pi * (δ / (1 + δ)) * Real.exp (-(1 + δ) * |ξ|) * Real.cos (γ * ξ))
      = 4 * Real.pi * (δ / (1 + δ)) *
          (Real.exp (-t * |ξ|) * Real.exp (-(1 + δ) * |ξ|)) * Real.cos (γ * ξ) := by ring
    _ = 4 * Real.pi * (δ / (1 + δ)) * Real.exp (-(t + 1 + δ) * |ξ|) * Real.cos (γ * ξ) := by
      rw [hexp]

lemma atomicFourierLaplaceFingerprint_formula (γ δ t ξ s : ℝ) (hs : s = |ξ|) :
    atomicFourierLaplaceFingerprint γ δ t ξ s =
      4 * Real.pi * (δ / (1 + δ)) * Real.exp (-s * δ) * Real.cos (γ * ξ) := by
  have hexp :
      Real.exp ((t + 1) * |ξ|) * Real.exp (-(t + 1 + δ) * |ξ|) = Real.exp (-|ξ| * δ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [atomicFourierLaplaceFingerprint, shiftedPoissonSmoothedAtom_formula]
  rw [hs]
  calc
    Real.exp ((t + 1) * |ξ|) *
        (4 * Real.pi * (δ / (1 + δ)) * Real.exp (-(t + 1 + δ) * |ξ|) * Real.cos (γ * ξ))
      = 4 * Real.pi * (δ / (1 + δ)) *
          (Real.exp ((t + 1) * |ξ|) * Real.exp (-(t + 1 + δ) * |ξ|)) * Real.cos (γ * ξ) := by
            ring
    _ = 4 * Real.pi * (δ / (1 + δ)) * Real.exp (-|ξ| * δ) * Real.cos (γ * ξ) := by rw [hexp]
    _ = 4 * Real.pi * (δ / (1 + δ)) * Real.exp (-|ξ| * δ) * Real.cos (γ * ξ) := rfl

lemma zeroFrequencyFingerprint_injective {δ δ' : ℝ}
    (_hδ : 0 < δ) (hδ' : 0 < δ')
    (h0 : zeroFrequencyFingerprint δ 0 = zeroFrequencyFingerprint δ' 0)
    (h1 : zeroFrequencyFingerprint δ 1 = zeroFrequencyFingerprint δ' 1) :
    δ = δ' := by
  have hc :
      4 * Real.pi * (δ / (1 + δ)) = 4 * Real.pi * (δ' / (1 + δ')) := by
    simpa [zeroFrequencyFingerprint] using h0
  have hexp : Real.exp (-δ) = Real.exp (-δ') := by
    have hcoeff_ne : 4 * Real.pi * (δ' / (1 + δ')) ≠ 0 := by
      have hδ1 : 0 < 1 + δ' := by linarith
      positivity
    have h1' :
        4 * Real.pi * (δ' / (1 + δ')) * Real.exp (-δ) =
          4 * Real.pi * (δ' / (1 + δ')) * Real.exp (-δ') := by
      simpa [zeroFrequencyFingerprint, hc] using h1
    exact mul_left_cancel₀ hcoeff_ne h1'
  have hneg : -δ = -δ' := Real.exp_injective hexp
  linarith

/-- Paper-facing atomic Fourier-Laplace tomography package: the shifted Poisson atom factors into
the Poisson smoothing multiplier and the Laplace weight, and the zero-frequency two-point trace
already determines the defect height `δ` for a unit-mass atom.
    prop:discussion-defect-measure-fourier-laplace -/
theorem paper_discussion_defect_measure_fourier_laplace
    (γ δ t ξ s : ℝ) (hδ : 0 < δ) (hs : s = |ξ|) :
    shiftedPoissonSmoothedAtom γ δ t ξ =
      4 * Real.pi * (δ / (1 + δ)) * Real.exp (-(t + 1 + δ) * |ξ|) * Real.cos (γ * ξ) ∧
      atomicFourierLaplaceFingerprint γ δ t ξ s =
        4 * Real.pi * (δ / (1 + δ)) * Real.exp (-s * δ) * Real.cos (γ * ξ) ∧
      (∀ δ' : ℝ, 0 < δ' →
        atomicFourierLaplaceFingerprint 0 δ t 0 0 =
            atomicFourierLaplaceFingerprint 0 δ' t 0 0 →
          atomicFourierLaplaceFingerprint 0 δ t 1 1 =
            atomicFourierLaplaceFingerprint 0 δ' t 1 1 →
          δ' = δ) := by
  refine ⟨shiftedPoissonSmoothedAtom_formula γ δ t ξ,
    atomicFourierLaplaceFingerprint_formula γ δ t ξ s hs, ?_⟩
  intro δ' hδ' h0 h1
  have hδ0 :
      atomicFourierLaplaceFingerprint 0 δ t 0 0 =
        4 * Real.pi * (δ / (1 + δ)) * Real.exp (-0 * δ) * Real.cos (0 * 0) :=
    atomicFourierLaplaceFingerprint_formula 0 δ t 0 0 (by simp)
  have hδ'0 :
      atomicFourierLaplaceFingerprint 0 δ' t 0 0 =
        4 * Real.pi * (δ' / (1 + δ')) * Real.exp (-0 * δ') * Real.cos (0 * 0) :=
    atomicFourierLaplaceFingerprint_formula 0 δ' t 0 0 (by simp)
  have hδ1 :
      atomicFourierLaplaceFingerprint 0 δ t 1 1 =
        4 * Real.pi * (δ / (1 + δ)) * Real.exp (-1 * δ) * Real.cos (0 * 1) :=
    atomicFourierLaplaceFingerprint_formula 0 δ t 1 1 (by simp)
  have hδ'1 :
      atomicFourierLaplaceFingerprint 0 δ' t 1 1 =
        4 * Real.pi * (δ' / (1 + δ')) * Real.exp (-1 * δ') * Real.cos (0 * 1) :=
    atomicFourierLaplaceFingerprint_formula 0 δ' t 1 1 (by simp)
  have h0' : zeroFrequencyFingerprint δ 0 = zeroFrequencyFingerprint δ' 0 := by
    calc
      zeroFrequencyFingerprint δ 0 = atomicFourierLaplaceFingerprint 0 δ t 0 0 := by
        simpa [zeroFrequencyFingerprint] using hδ0.symm
      _ = atomicFourierLaplaceFingerprint 0 δ' t 0 0 := h0
      _ = zeroFrequencyFingerprint δ' 0 := by
        simpa [zeroFrequencyFingerprint] using hδ'0
  have h1' : zeroFrequencyFingerprint δ 1 = zeroFrequencyFingerprint δ' 1 := by
    calc
      zeroFrequencyFingerprint δ 1 = atomicFourierLaplaceFingerprint 0 δ t 1 1 := by
        simpa [zeroFrequencyFingerprint] using hδ1.symm
      _ = atomicFourierLaplaceFingerprint 0 δ' t 1 1 := h1
      _ = zeroFrequencyFingerprint δ' 1 := by
        simpa [zeroFrequencyFingerprint] using hδ'1
  exact (zeroFrequencyFingerprint_injective hδ hδ' h0' h1').symm

end Omega.Discussion
