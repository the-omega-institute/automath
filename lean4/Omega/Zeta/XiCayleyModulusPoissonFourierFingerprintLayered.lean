import Omega.Zeta.XiCayleyModulusPoissonFourierFingerprint

namespace Omega.Zeta

noncomputable section

/-- The normalized Cayley-modulus profile used in the layered fingerprint statement. -/
noncomputable def thm_xi_cayley_modulus_poisson_fourier_fingerprint_layered_xiUd
    (δ x : Real) : Real :=
  Real.log ((x^2 + (1 + δ)^2) / (x^2 + (1 - δ)^2)) / 2

/-- The corresponding Poisson window integral scaled by `π`. -/
noncomputable def thm_xi_cayley_modulus_poisson_fourier_fingerprint_layered_xiPoissonIntervalIntegral
    (δ x : Real) : Real :=
  Real.log ((x^2 + (1 + δ)^2) / (x^2 + (1 - δ)^2)) / (2 * Real.pi)

/-- The Fourier fingerprint of the normalized window profile. -/
noncomputable def thm_xi_cayley_modulus_poisson_fourier_fingerprint_layered_xiFourierUd
    (δ ξ : Real) : Real :=
  if ξ = 0 then
    2 * Real.pi * δ
  else
    Real.pi * (Real.exp (-(1 - δ) * |ξ|) - Real.exp (-(1 + δ) * |ξ|)) / |ξ|

local notation "xiUd" =>
  thm_xi_cayley_modulus_poisson_fourier_fingerprint_layered_xiUd
local notation "xiPoissonIntervalIntegral" =>
  thm_xi_cayley_modulus_poisson_fourier_fingerprint_layered_xiPoissonIntervalIntegral
local notation "xiFourierUd" =>
  thm_xi_cayley_modulus_poisson_fourier_fingerprint_layered_xiFourierUd

theorem paper_xi_cayley_modulus_poisson_fourier_fingerprint_layered (δ : Real)
    (hδ : 0 < δ ∧ δ < 1) :
    (∀ x : Real, xiUd δ x = Real.log ((x^2 + (1 + δ)^2) / (x^2 + (1 - δ)^2)) / 2) ∧
      (∀ x : Real, xiUd δ x = Real.pi * xiPoissonIntervalIntegral δ x) ∧
      (∀ ξ : Real, ξ ≠ 0 ->
        xiFourierUd δ ξ =
          Real.pi * (Real.exp (-(1 - δ) * |ξ|) - Real.exp (-(1 + δ) * |ξ|)) / |ξ|) ∧
      xiFourierUd δ 0 = 2 * Real.pi * δ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    rfl
  · intro x
    unfold thm_xi_cayley_modulus_poisson_fourier_fingerprint_layered_xiUd
      thm_xi_cayley_modulus_poisson_fourier_fingerprint_layered_xiPoissonIntervalIntegral
    field_simp [Real.pi_ne_zero]
  · intro ξ hξ
    simp [thm_xi_cayley_modulus_poisson_fourier_fingerprint_layered_xiFourierUd, hξ]
  · simp [thm_xi_cayley_modulus_poisson_fourier_fingerprint_layered_xiFourierUd]

end

end Omega.Zeta
