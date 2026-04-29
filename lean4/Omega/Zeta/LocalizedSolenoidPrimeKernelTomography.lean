import Mathlib.Tactic
import Omega.Zeta.LocalizedSolenoidMultiplicationKernelDegree

namespace Omega.Zeta

/-- Paper label: `cor:xi-localized-solenoid-prime-kernel-tomography`. -/
theorem paper_xi_localized_solenoid_prime_kernel_tomography
    (S : FinitePrimeLocalization) :
    ∀ ⦃q : ℕ⦄, Nat.Prime q →
      Nat.card (xi_localized_solenoid_multiplication_kernel_degree_kernelModel S q) =
          (if q ∈ S then 1 else q) ∧
        (q ∈ S ↔
          Nat.card (xi_localized_solenoid_multiplication_kernel_degree_kernelModel S q) = 1) := by
  intro q hq
  rcases paper_xi_localized_solenoid_multiplication_kernel_degree S hq with
    ⟨_, ⟨hIn, hOut⟩, _, hCard⟩
  have hCardIndex :
      Nat.card (xi_localized_solenoid_multiplication_kernel_degree_kernelModel S q) =
        localizedIndex S q := by
    rw [xi_localized_solenoid_multiplication_kernel_degree_coverDegree] at hCard
    exact hCard
  constructor
  · by_cases hqS : q ∈ S
    · simp [hqS, hCardIndex, hIn.mp hqS]
    · simp [hqS, hCardIndex, hOut.mp hqS]
  · constructor
    · intro hqS
      simpa [hCardIndex] using hIn.mp hqS
    · intro hCardOne
      by_contra hqS
      have hq_eq_one : q = 1 := by
        exact (hCardIndex.trans (hOut.mp hqS)).symm.trans hCardOne
      exact hq.ne_one hq_eq_one

end Omega.Zeta
