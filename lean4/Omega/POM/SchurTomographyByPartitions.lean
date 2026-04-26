import Omega.POM.SchurTomographyInversePartitionMonomials

namespace Omega.POM

/-- Paper label: `prop:pom-schur-tomography-by-partitions`. The historical inverse-tomography
package already stores the forward partition-indexed Schur tomography statement, so the paper-facing
wrapper is its direct projection. -/
theorem paper_pom_schur_tomography_by_partitions
    (D : SchurTomographyInversePartitionMonomialsData) : D.forwardSchurTomography := by
  exact D.forwardSchurTomography_h

end Omega.POM
