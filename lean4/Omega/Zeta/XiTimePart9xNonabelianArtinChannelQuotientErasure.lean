import Omega.EA.KernelArtinFactorization
import Omega.Zeta.XiTimePart64NonabelianQuotientEnergyLossExact

namespace Omega.Zeta

/-- Paper label:
`thm:xi-time-part9x-nonabelian-artin-channel-quotient-erasure`.
The concrete Artin determinant/zeta factorization and the exact nonabelian quotient energy-loss
package give the determinant--energy erasure wrapper. -/
theorem paper_xi_time_part9x_nonabelian_artin_channel_quotient_erasure :
    (∀ m t u v,
        Omega.EA.kernelArtinDetFactorization m t u v ∧
          Omega.EA.kernelArtinZetaFactorization t u v) ∧
      Omega.Zeta.paper_xi_time_part64_nonabelian_quotient_energy_loss_exact := by
  refine ⟨?_, ?_⟩
  · intro m t u v
    exact Omega.EA.paper_kernel_artin_factorization m t u v
  · simpa [Omega.Zeta.paper_xi_time_part64_nonabelian_quotient_energy_loss_exact] using
      Omega.Zeta.xi_time_part64_nonabelian_quotient_energy_loss_exact_statement_holds

end Omega.Zeta
