import Mathlib.Tactic
import Omega.Zeta.ReciprocalPlusKernelRhImpliesToyRh
import Omega.Zeta.XiEndpointAbsorptionAdamsRescaling

namespace Omega.Zeta

open ReciprocalPlusKernelRhImpliesToyRhData

/-- Paper label: `thm:xi-multiscale-consistency-implies-rh`.

Odd Adams rescaling multiplies the `-1` endpoint absorption by the scale `m`. If that endpoint is
multiscale-consistent across all odd scales, the only possibility is `Φ₋₁ = 0`. Combining this
with the normalized endpoint value `B(-1) = 1` and the existing reciprocal kernel-RH bridge gives
the RH conclusion packaged here as the toy-RH critical-circle statement. -/
theorem paper_xi_multiscale_consistency_implies_rh
    (D : ReciprocalPlusKernelRhImpliesToyRhData)
    (phiMinus phiPlus : ℚ)
    (hkernel : D.kernelRh)
    (hplus : phiPlus = 1)
    (hcons :
      ∀ m, Odd m →
        xiEndpointAbsorptionAfterAdams m phiMinus phiPlus XiEndpointChannel.minusOne = phiMinus) :
    phiMinus = 0 ∧ phiPlus = 1 ∧ D.toyRh := by
  have hscale :=
    (paper_xi_endpoint_absorption_adams_rescaling 3 (by omega) phiMinus phiPlus).1
  have hfixed :
      xiEndpointAbsorptionAfterAdams 3 phiMinus phiPlus XiEndpointChannel.minusOne = phiMinus :=
    hcons 3 (by decide)
  have hphi : phiMinus = 0 := by
    rw [if_pos (by decide)] at hscale
    rw [hfixed] at hscale
    ring_nf at hscale
    linarith
  have htoy : D.toyRh := (paper_reciprocal_plus_kernel_rh_implies_toy_rh D).1 hkernel
  exact ⟨hphi, hplus, htoy⟩

end Omega.Zeta
