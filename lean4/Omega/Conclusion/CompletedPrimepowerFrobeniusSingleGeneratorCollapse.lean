import Omega.Conclusion.CompletedPrimeLengthFrobeniusCollapse
import Omega.Conclusion.CompletedPrimepowerDworkFrobeniusTower

namespace Omega.Conclusion

open Omega.Zeta
open Omega.Zeta.DerivedPrimePowerDworkFrobeniusTowerData
open Omega.DerivedConsequences

/-- Concrete statement for the prime-power completed Frobenius tower collapsing modulo `p` to the
single seed residue. -/
def conclusion_completed_primepower_frobenius_single_generator_collapse_statement :
    Prop :=
  ∀ D : DerivedPrimePowerDworkFrobeniusTowerData,
    derived_prime_length_completed_frobenius_collapse_statement D ∧
      D.integralCongruenceLaw ∧
      D.modpFrobeniusCollapseLaw ∧
      (∀ k : ℕ, D.tower k % D.p = D.tower 1 % D.p)

/-- Paper label:
`thm:conclusion-completed-primepower-frobenius-single-generator-collapse`. -/
theorem paper_conclusion_completed_primepower_frobenius_single_generator_collapse :
    conclusion_completed_primepower_frobenius_single_generator_collapse_statement := by
  intro D
  rcases conclusion_completed_primepower_dwork_frobenius_tower_verified D with
    ⟨hprimeLength, hintegral, hcollapse⟩
  refine ⟨hprimeLength, hintegral, hcollapse, ?_⟩
  intro k
  calc
    D.tower k % D.p = D.seed % D.p := hcollapse k
    _ = D.tower 1 % D.p := (hcollapse 1).symm

end Omega.Conclusion
