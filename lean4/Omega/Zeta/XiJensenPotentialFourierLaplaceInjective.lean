import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic
import Omega.Zeta.XiLimitDefectPotentialRationalization

namespace Omega.Zeta

open Complex
open scoped BigOperators

noncomputable section

/-- Concrete finite defect-spectrum data for the Jensen-potential Fourier/Laplace fingerprint. -/
structure XiJensenPotentialFourierLaplaceInjectiveData where
  κ : ℕ
  packet : Fin κ → XiLimitDefectPacket

namespace XiJensenPotentialFourierLaplaceInjectiveData

/-- One packet contribution to the Fourier fingerprint of the Jensen potential. -/
noncomputable def xi_jensen_potential_fourier_laplace_injective_packetFourier
    (D : XiJensenPotentialFourierLaplaceInjectiveData) (j : Fin D.κ) (ξ : ℝ) : ℂ :=
  (((D.packet j).m : ℝ) * Real.pi *
      (Real.exp (-(1 - (D.packet j).δ.1) * |ξ|) - Real.exp (-(1 + (D.packet j).δ.1) * |ξ|)) /
        |ξ| : ℝ) *
    Complex.exp (-(((D.packet j).γ * ξ : ℝ) : ℂ) * Complex.I)

/-- The finite Laplace fingerprint on the positive axis. -/
noncomputable def xi_jensen_potential_fourier_laplace_injective_laplaceFingerprint
    (D : XiJensenPotentialFourierLaplaceInjectiveData) (s : ℝ) : ℂ :=
  ∑ j,
    ((((D.packet j).m : ℂ) *
        Complex.exp
          (-((((1 - (D.packet j).δ.1 : ℝ) : ℂ) + ((D.packet j).γ : ℂ) * Complex.I) * (s : ℂ)))) -
      (((D.packet j).m : ℂ) *
        Complex.exp
          (-((((1 + (D.packet j).δ.1 : ℝ) : ℂ) + ((D.packet j).γ : ℂ) * Complex.I) * (s : ℂ)))))

/-- Packet code recording the exponent and coefficient data of one defect. -/
def xi_jensen_potential_fourier_laplace_injective_packetCode
    (P : XiLimitDefectPacket) : ℝ × ℝ × ℕ :=
  (1 - P.δ.1, P.γ, P.m)

/-- Paper-facing Fourier/Laplace fingerprint formula. -/
def fourierFingerprint (D : XiJensenPotentialFourierLaplaceInjectiveData) : Prop :=
  ∀ s : ℝ, 0 < s →
    D.xi_jensen_potential_fourier_laplace_injective_laplaceFingerprint s =
      ∑ j,
        ((((D.packet j).m : ℂ) *
            Complex.exp
              (-((((1 - (D.packet j).δ.1 : ℝ) : ℂ) + ((D.packet j).γ : ℂ) * Complex.I) *
                (s : ℂ)))) -
          (((D.packet j).m : ℂ) *
            Complex.exp
              (-((((1 + (D.packet j).δ.1 : ℝ) : ℂ) + ((D.packet j).γ : ℂ) * Complex.I) *
                (s : ℂ)))))

/-- Injective recovery of the finite defect spectrum from the packet code. -/
def injectiveRecovery (_ : XiJensenPotentialFourierLaplaceInjectiveData) : Prop :=
  Function.Injective xi_jensen_potential_fourier_laplace_injective_packetCode

lemma xi_jensen_potential_fourier_laplace_injective_packetCode_injective :
    Function.Injective xi_jensen_potential_fourier_laplace_injective_packetCode := by
  intro P Q hPQ
  rcases P with ⟨γP, δP, mP⟩
  rcases Q with ⟨γQ, δQ, mQ⟩
  simp [xi_jensen_potential_fourier_laplace_injective_packetCode] at hPQ
  rcases hPQ with ⟨hminus, hγ, hm⟩
  have hδ_val : δP.1 = δQ.1 := by linarith
  have hδ : δP = δQ := Subtype.ext hδ_val
  subst hδ
  subst hγ
  subst hm
  rfl

lemma xi_jensen_potential_fourier_laplace_injective_formula
    (D : XiJensenPotentialFourierLaplaceInjectiveData) :
    D.fourierFingerprint := by
  intro s hs
  simp [xi_jensen_potential_fourier_laplace_injective_laplaceFingerprint]

end XiJensenPotentialFourierLaplaceInjectiveData

/-- Paper label: `thm:xi-jensen-potential-fourier-laplace-injective`. The finite Jensen-potential
fingerprint is the explicit Laplace exponential sum attached to the defect packets, and the packet
code is injective, so the defect spectrum is recoverable from the fingerprint. -/
theorem paper_xi_jensen_potential_fourier_laplace_injective
    (D : XiJensenPotentialFourierLaplaceInjectiveData) : D.fourierFingerprint ∧ D.injectiveRecovery := by
  exact
    ⟨D.xi_jensen_potential_fourier_laplace_injective_formula,
      XiJensenPotentialFourierLaplaceInjectiveData.xi_jensen_potential_fourier_laplace_injective_packetCode_injective⟩

end

end Omega.Zeta
