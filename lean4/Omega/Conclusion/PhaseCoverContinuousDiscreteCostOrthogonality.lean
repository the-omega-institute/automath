import Omega.Conclusion.TorusCoverDegreePotentialIdentity
import Omega.Conclusion.CoverKernelMinPrimeLedgerSignature

namespace Omega.Conclusion

open conclusion_torus_cover_degree_potential_identity_Data

/-- Paper label: `thm:conclusion-phase-cover-continuous-discrete-cost-orthogonality`. -/
theorem paper_conclusion_phase_cover_continuous_discrete_cost_orthogonality
    (T : conclusion_torus_cover_degree_potential_identity_Data)
    (kernelEmbedsTorsion finiteLedgerLowerBound lowerBoundAttained primeSupportForced : Prop)
    (hKernel : kernelEmbedsTorsion)
    (hFinite : kernelEmbedsTorsion → finiteLedgerLowerBound)
    (hAttain : lowerBoundAttained)
    (hPrime : kernelEmbedsTorsion → primeSupportForced) :
    T.expectedPrecisionPotentialEqualsLogDegree ∧
      kernelEmbedsTorsion ∧
        finiteLedgerLowerBound ∧ lowerBoundAttained ∧ primeSupportForced := by
  rcases paper_conclusion_torus_cover_degree_potential_identity T with ⟨_, hExpected⟩
  rcases paper_conclusion_cover_kernel_min_prime_ledger_signature
      kernelEmbedsTorsion finiteLedgerLowerBound lowerBoundAttained primeSupportForced
      hKernel hFinite hAttain hPrime with
    ⟨hKernel', hFinite', hAttain', hPrime'⟩
  exact ⟨hExpected, hKernel', hFinite', hAttain', hPrime'⟩

end Omega.Conclusion
