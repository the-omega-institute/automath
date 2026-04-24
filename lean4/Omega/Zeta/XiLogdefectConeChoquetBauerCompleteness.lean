import Mathlib.Tactic
import Omega.Zeta.XiLogDefectAffineReproducingMomentIdentities
import Omega.Zeta.XiLogdefectBandpassPoissonRepresentation

namespace Omega.Zeta

/-- Finite-support completeness package for the log-defect cone: the finite bandpass potential
    has its Poisson representation, the affine moments are explicit, single-kernel parameters are
    rigidly recovered from the zeroth and first moments, and the singleton finite rays coincide
    with the one-kernel generators.
    thm:xi-logdefect-cone-choquet-bauer-completeness -/
def XiLogdefectChoquetBauerFiniteCompleteness : Prop :=
  (∀ {n : ℕ} (x y0 y1 : ℝ) (center weight : Fin n → ℝ) (_hy0 : 0 < y0) (_hy1 : 0 < y1),
    xiLogdefectBandpassPotential x y0 y1 center (xiLogdefectBandpassSigma weight) =
      xiLogdefectBandpassPoissonDecomposition x y0 y1 center weight) ∧
  (∀ γ δ, 0 < δ → δ ≤ 1 / 2 →
    ∀ x, xiLogdefectAffineKernel γ δ x = xiLogdefectAffinePoissonKernel γ δ x) ∧
  (∀ γ δ, xiLogdefectAffineZerothMoment γ δ = 2 * Real.pi * δ) ∧
  (∀ γ δ, xiLogdefectAffineFirstMoment γ δ = 2 * Real.pi * δ * γ) ∧
  (∀ γ₁ γ₂ δ₁ δ₂, 0 < δ₁ → 0 < δ₂ →
    xiLogdefectAffineZerothMoment γ₁ δ₁ = xiLogdefectAffineZerothMoment γ₂ δ₂ →
    xiLogdefectAffineFirstMoment γ₁ δ₁ = xiLogdefectAffineFirstMoment γ₂ δ₂ →
    δ₁ = δ₂ ∧ γ₁ = γ₂) ∧
  (∀ γ δ x,
    xiLogdefectFinitePotential x (fun _ : Fin 1 => γ) (fun _ => δ) (fun _ => (1 : ℝ)) =
      xiLogdefectAffineKernel γ δ x) ∧
  (∀ γ δ,
    xiLogdefectFiniteZerothMoment (fun _ : Fin 1 => γ) (fun _ => δ) (fun _ => (1 : ℝ)) =
        xiLogdefectAffineZerothMoment γ δ ∧
      xiLogdefectFiniteFirstMoment (fun _ : Fin 1 => γ) (fun _ => δ) (fun _ => (1 : ℝ)) =
        xiLogdefectAffineFirstMoment γ δ)

set_option maxHeartbeats 400000 in
theorem paper_xi_logdefect_cone_choquet_bauer_completeness :
    XiLogdefectChoquetBauerFiniteCompleteness := by
  rcases paper_xi_logdefect_affine_reproducing_moment_identities with
    ⟨hAffineKernel, hZeroth, hFirst, _hAffineMoment, _hFiniteKernel, _hFiniteZeroth,
      _hFiniteFirst, _hFiniteAffine⟩
  refine ⟨?_, hAffineKernel, hZeroth, hFirst, ?_, ?_, ?_⟩
  · intro n x y0 y1 center weight hy0 hy1
    exact paper_xi_logdefect_bandpass_poisson_representation x y0 y1 center weight hy0 hy1
  · intro γ₁ γ₂ δ₁ δ₂ hδ₁ hδ₂ hZeroEq hFirstEq
    have hscaledZero : 2 * Real.pi * δ₁ = 2 * Real.pi * δ₂ := by
      simpa [hZeroth γ₁ δ₁, hZeroth γ₂ δ₂] using hZeroEq
    have hδ : δ₁ = δ₂ := by
      have hpi : 0 < 2 * Real.pi := by positivity
      nlinarith
    have hscaledFirst : (2 * Real.pi * δ₁) * γ₁ = (2 * Real.pi * δ₁) * γ₂ := by
      have hfirstScaled : 2 * Real.pi * δ₁ * γ₁ = 2 * Real.pi * δ₂ * γ₂ := by
        simpa [hFirst γ₁ δ₁, hFirst γ₂ δ₂, mul_assoc] using hFirstEq
      simpa [hδ, mul_assoc] using hfirstScaled
    have hγ : γ₁ = γ₂ := by
      have hcoeff : 0 < 2 * Real.pi * δ₁ := by positivity
      nlinarith
    exact ⟨hδ, hγ⟩
  · intro γ δ x
    simp [xiLogdefectFinitePotential, xiLogdefectAffineKernel]
  · intro γ δ
    constructor
    · simp [xiLogdefectFiniteZerothMoment]
    · simp [xiLogdefectFiniteFirstMoment, xiLogdefectAffineFirstMoment,
        xiLogdefectAffineZerothMoment]

end Omega.Zeta
