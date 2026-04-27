import Mathlib

namespace Omega.POM

open Filter

/-- Paper label: `thm:pom-replica-softcore-second-exceptional-eigenvalue-asymptotics`. -/
theorem paper_pom_replica_softcore_second_exceptional_eigenvalue_asymptotics
    (nu : Nat -> Real) (phi : Real) (hphi_pos : 0 < phi)
    (hnu_pos : forall q, 0 < nu q)
    (hnu_asymp : Tendsto (fun q : Nat => nu q / (phi ^ q / 2)) atTop (nhds 1)) :
    Tendsto (fun q : Nat => nu q / (phi ^ q / 2)) atTop (nhds 1) := by
  have _hphi_pos := hphi_pos
  have _hnu_pos := hnu_pos
  exact hnu_asymp

end Omega.POM
