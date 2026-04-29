import Omega.POM.SchurTomographyInversePartitionMonomials

namespace Omega.POM

/-- Paper-facing two-way trace/moment equivalence extracted from the inverse Schur tomography
package.
    cor:pom-schur-traces-moments-bijection -/
theorem paper_pom_schur_traces_moments_bijection
    (D : SchurTomographyInversePartitionMonomialsData) :
    D.forwardSchurTomography ∧ D.partitionMonomialRecovered := by
  have h := paper_pom_schur_tomography_inverse_partition_monomials D
  exact ⟨h.1, h.2.2⟩

end Omega.POM
