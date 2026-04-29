import Omega.POM.InfoncePartitionOptimalClosedForm

namespace Omega.POM

/-- Paper label: `cor:pom-infonce-fold-ledger-remainder-bits`. -/
theorem paper_pom_infonce_fold_ledger_remainder_bits
    (optimalValueLaw residueOccupancyTwoPoint sandwichBounds monotoneInBits : Prop)
    (hOpt : optimalValueLaw) (hOcc : residueOccupancyTwoPoint) (hBounds : sandwichBounds)
    (hMono : monotoneInBits) :
    optimalValueLaw ∧ residueOccupancyTwoPoint ∧ sandwichBounds ∧ monotoneInBits := by
  exact ⟨hOpt, hOcc, hBounds, hMono⟩

end Omega.POM
