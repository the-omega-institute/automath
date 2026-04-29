import Mathlib.Data.Finset.Basic
import Omega.Conclusion.LocalizedDualPrimesupportFunctoriality

namespace Omega.Conclusion

/-- The profinite residue support left behind by the connected compensation quotient is the set of
localized primes removed by the quotient map. -/
def conclusion_connected_compensation_axis_at_most_one_dimensional_kernel_prime_support
    (S T : Omega.Zeta.FinitePrimeLocalization) : Finset ℕ :=
  S \ T

/-- Paper label: `thm:conclusion-connected-compensation-axis-at-most-one-dimensional`. In the
finite localized-dual surrogate, every connected compensation quotient has circle dimension at
most `1`, the dual surjection forces the target prime support to lie inside the source support,
and the discarded primes are exactly the profinite residue support retained by the kernel. -/
theorem paper_conclusion_connected_compensation_axis_at_most_one_dimensional
    (S T : Omega.Zeta.FinitePrimeLocalization)
    (hSurj : conclusion_localized_dual_primesupport_functoriality_surjectiveModel S T) :
    Omega.Zeta.localizedIntegersCircleDimension T ≤ 1 ∧
      T ⊆ S ∧
      ∀ p : ℕ,
        p ∈ conclusion_connected_compensation_axis_at_most_one_dimensional_kernel_prime_support S T ↔
          p ∈ S ∧ p ∉ T := by
  have hTS : T ⊆ S :=
    ((paper_conclusion_localized_dual_primesupport_functoriality S T).1).mp hSurj
  refine ⟨?_, hTS, ?_⟩
  · simp [Omega.Zeta.localizedIntegersCircleDimension]
  · intro p
    simp [conclusion_connected_compensation_axis_at_most_one_dimensional_kernel_prime_support]

end Omega.Conclusion
