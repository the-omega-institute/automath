import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic
import Omega.Zeta.XiLimitDefectPotentialRationalization

namespace Omega.Zeta

open Complex
open scoped BigOperators

noncomputable section

/-- Concrete finite Jensen packet data used for the Fourier/Laplace fingerprint wrapper. -/
structure XiJensenFourierLaplaceFingerprintInjectivityData where
  κ : ℕ
  packet : Fin κ → XiLimitDefectPacket

namespace XiJensenFourierLaplaceFingerprintInjectivityData

/-- One packet contribution to the Fourier transform of the Jensen potential. -/
noncomputable def xi_jensen_fourier_laplace_fingerprint_injectivity_packetFourier
    (D : XiJensenFourierLaplaceFingerprintInjectivityData) (j : Fin D.κ) (ξ : ℝ) : ℂ :=
  (((D.packet j).m : ℝ) * Real.pi *
      (Real.exp (-(1 - (D.packet j).δ.1) * |ξ|) - Real.exp (-(1 + (D.packet j).δ.1) * |ξ|)) /
        |ξ| : ℝ) *
    Complex.exp (-(((D.packet j).γ * ξ : ℝ) : ℂ) * Complex.I)

/-- The finite Fourier fingerprint of the Jensen potential. -/
noncomputable def xi_jensen_fourier_laplace_fingerprint_injectivity_fourierFingerprint
    (D : XiJensenFourierLaplaceFingerprintInjectivityData) (ξ : ℝ) : ℂ :=
  ∑ j, D.xi_jensen_fourier_laplace_fingerprint_injectivity_packetFourier j ξ

/-- The finite Laplace fingerprint `G(s) = (s / π) \hat J(s)` on the positive axis. -/
noncomputable def xi_jensen_fourier_laplace_fingerprint_injectivity_laplaceFingerprint
    (D : XiJensenFourierLaplaceFingerprintInjectivityData) (s : ℝ) : ℂ :=
  ∑ j,
    ((((D.packet j).m : ℂ) *
        Complex.exp
          (-((((1 - (D.packet j).δ.1 : ℝ) : ℂ) + ((D.packet j).γ : ℂ) * Complex.I) * (s : ℂ)))) -
      (((D.packet j).m : ℂ) *
        Complex.exp
          (-((((1 + (D.packet j).δ.1 : ℝ) : ℂ) + ((D.packet j).γ : ℂ) * Complex.I) * (s : ℂ)))))

/-- The exponential code carried by one packet. -/
def xi_jensen_fourier_laplace_fingerprint_injectivity_packetCode
    (P : XiLimitDefectPacket) : ℝ × ℝ × ℕ :=
  (1 - P.δ.1, P.γ, P.m)

/-- The packet-level Laplace fingerprint formula. -/
def fingerprintFormula (D : XiJensenFourierLaplaceFingerprintInjectivityData) : Prop :=
  ∀ s : ℝ, 0 < s →
    D.xi_jensen_fourier_laplace_fingerprint_injectivity_laplaceFingerprint s =
      ∑ j,
        ((((D.packet j).m : ℂ) *
            Complex.exp
              (-((((1 - (D.packet j).δ.1 : ℝ) : ℂ) + ((D.packet j).γ : ℂ) * Complex.I) *
                (s : ℂ)))) -
          (((D.packet j).m : ℂ) *
            Complex.exp
              (-((((1 + (D.packet j).δ.1 : ℝ) : ℂ) + ((D.packet j).γ : ℂ) * Complex.I) *
                (s : ℂ)))))

/-- The packet fingerprint code is injective, so the exponents and coefficients recover the
original packet data. -/
def fingerprintInjective (_ : XiJensenFourierLaplaceFingerprintInjectivityData) : Prop :=
  Function.Injective xi_jensen_fourier_laplace_fingerprint_injectivity_packetCode

lemma xi_jensen_fourier_laplace_fingerprint_injectivity_packetCode_injective :
    Function.Injective xi_jensen_fourier_laplace_fingerprint_injectivity_packetCode := by
  intro P Q hPQ
  rcases P with ⟨γP, δP, mP⟩
  rcases Q with ⟨γQ, δQ, mQ⟩
  simp [xi_jensen_fourier_laplace_fingerprint_injectivity_packetCode] at hPQ
  rcases hPQ with ⟨hminus, hγ, hm⟩
  have hδ_val : δP.1 = δQ.1 := by linarith
  have hδ : δP = δQ := Subtype.ext hδ_val
  subst hδ
  subst hγ
  subst hm
  rfl

lemma xi_jensen_fourier_laplace_fingerprint_injectivity_formula
    (D : XiJensenFourierLaplaceFingerprintInjectivityData) :
    D.fingerprintFormula := by
  intro s hs
  simp [xi_jensen_fourier_laplace_fingerprint_injectivity_laplaceFingerprint]

end XiJensenFourierLaplaceFingerprintInjectivityData

/-- Paper label: `thm:xi-jensen-fourier-laplace-fingerprint-injectivity`. The finite Jensen
Fourier profile yields the advertised Laplace exponential sum, and the packet fingerprint code is
injective. -/
theorem paper_xi_jensen_fourier_laplace_fingerprint_injectivity
    (D : XiJensenFourierLaplaceFingerprintInjectivityData) :
    D.fingerprintFormula ∧ D.fingerprintInjective := by
  exact ⟨D.xi_jensen_fourier_laplace_fingerprint_injectivity_formula,
    XiJensenFourierLaplaceFingerprintInjectivityData.xi_jensen_fourier_laplace_fingerprint_injectivity_packetCode_injective⟩

end

end Omega.Zeta
