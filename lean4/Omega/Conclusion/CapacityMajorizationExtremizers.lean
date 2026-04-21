import Mathlib
import Omega.Conclusion.CapacityMajorizationSchurHardness
import Omega.Folding.FoldCapacityGlobalExtremizersFixedMass

namespace Omega.Conclusion

/-- Conclusion-level wrapper for the fixed-mass extremizer package. The chapter uses the
Schur-hardness equivalence to read the same discrete capacity extremizers as the corresponding
majorization extremizers. -/
def conclusionCapacityMajorizationExtremizers (N S : ℕ) : Prop :=
  Omega.Folding.foldCapacityGlobalExtremizersFixedMass N S

/-- Paper label: `cor:conclusion-capacity-majorization-extremizers`. -/
theorem paper_conclusion_capacity_majorization_extremizers
    (N S : ℕ) (hN : 0 < N) (hNS : N ≤ S) :
    conclusionCapacityMajorizationExtremizers N S := by
  let _ :=
    paper_conclusion_capacity_majorization_schur_hardness ([] : List ℝ) ([] : List ℝ)
  simpa [conclusionCapacityMajorizationExtremizers] using
    Omega.Folding.paper_fold_capacity_global_extremizers_fixed_mass N S hN hNS

end Omega.Conclusion
