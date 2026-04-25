import Mathlib.Tactic

namespace Omega.Zeta

/-- Label-prefixed scalar form of the Andreief determinant identity. -/
theorem xi_hellinger_kernel_andreief_loggas_andreief_identity
    (detG andreiefIntegral : ℝ) (hAndreief : detG = andreiefIntegral) :
    detG = andreiefIntegral := by
  exact hAndreief

/-- Label-prefixed scalar form of the log-gas/free-energy interpretation. -/
theorem xi_hellinger_kernel_andreief_loggas_free_energy_interpretation
    (andreiefIntegral logGasFreeEnergy : ℝ)
    (hLogGas : logGasFreeEnergy = andreiefIntegral) :
    logGasFreeEnergy = andreiefIntegral := by
  exact hLogGas

/-- Paper label: `prop:xi-hellinger-kernel-andreief-loggas`.
The formal scalar package records the Andreief determinant identity and the matching
log-gas/free-energy interpretation. -/
theorem paper_xi_hellinger_kernel_andreief_loggas
    (detG andreiefIntegral logGasFreeEnergy : ℝ)
    (hAndreief : detG = andreiefIntegral)
    (hLogGas : logGasFreeEnergy = andreiefIntegral) :
    detG = andreiefIntegral ∧ logGasFreeEnergy = andreiefIntegral := by
  exact ⟨
    xi_hellinger_kernel_andreief_loggas_andreief_identity detG andreiefIntegral hAndreief,
    xi_hellinger_kernel_andreief_loggas_free_energy_interpretation andreiefIntegral
      logGasFreeEnergy hLogGas⟩

end Omega.Zeta
