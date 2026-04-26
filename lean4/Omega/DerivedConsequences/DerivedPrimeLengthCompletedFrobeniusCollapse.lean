import Omega.Zeta.DerivedPrimePowerDworkFrobeniusTower

namespace Omega.DerivedConsequences

open Omega.Zeta
open DerivedPrimePowerDworkFrobeniusTowerData

/-- First-stage collapse extracted from the prime-power Dwork tower. -/
def derived_prime_length_completed_frobenius_collapse_statement
    (D : DerivedPrimePowerDworkFrobeniusTowerData) : Prop :=
  D.tower 1 = D.seed + D.p * D.correction 0 ∧
    D.tower 1 % D.p = D.seed % D.p ∧
    D.tower 1 % D.p = D.tower 0 % D.p

/-- Paper label: `thm:derived-prime-length-completed-frobenius-collapse`. -/
theorem paper_derived_prime_length_completed_frobenius_collapse
    (D : DerivedPrimePowerDworkFrobeniusTowerData) :
    derived_prime_length_completed_frobenius_collapse_statement D := by
  rcases paper_derived_prime_power_dwork_frobenius_tower D with ⟨hintegral, hcollapse⟩
  refine ⟨?_, hcollapse 1, ?_⟩
  · simpa [D.tower_zero] using hintegral 0
  · calc
      D.tower 1 % D.p = D.seed % D.p := hcollapse 1
      _ = D.tower 0 % D.p := by simpa [D.tower_zero] using (hcollapse 0).symm

end Omega.DerivedConsequences
