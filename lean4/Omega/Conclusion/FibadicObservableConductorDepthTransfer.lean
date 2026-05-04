import Mathlib.Tactic
import Omega.Conclusion.FibadicFiniteValuedObservableConductor
import Omega.Conclusion.FibadicMinimalResolutionForPrimeRegisterPackage

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-fibadic-observable-conductor-depth-transfer`. -/
theorem paper_conclusion_fibadic_observable_conductor_depth_transfer
    (chi : conclusion_fibadic_finite_valued_observable_conductor_observable)
    (orders : List Nat) (d : Nat) (visible : Nat -> Prop)
    (hvisible : forall n, visible n <-> forall z, z ∈ orders -> z ∣ n)
    (hconductor : visible d) :
    visible d ∧ (visible d <-> orders.foldl Nat.lcm 1 ∣ d) := by
  have _ := chi
  exact ⟨hconductor,
    paper_conclusion_fibadic_minimal_resolution_for_prime_register_package orders d visible
      hvisible⟩

end Omega.Conclusion
