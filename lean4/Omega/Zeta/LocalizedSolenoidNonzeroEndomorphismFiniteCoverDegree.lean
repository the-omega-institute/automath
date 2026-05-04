import Omega.Zeta.LocalizedSolenoidMultiplicationKernelDegree

namespace Omega.Zeta

/-- Paper label: `cor:xi-localized-solenoid-nonzero-endomorphism-finite-cover-degree`.
The finite cover degree of multiplication by a positive integer on the localized solenoid is the
localized quotient index, and the finite cyclic kernel model has exactly that cardinality. -/
theorem paper_xi_localized_solenoid_nonzero_endomorphism_finite_cover_degree
    (S : Omega.Zeta.FinitePrimeLocalization) (n : ℕ) (hn : 0 < n) :
    Omega.Zeta.xi_localized_solenoid_multiplication_kernel_degree_coverDegree S n =
        Omega.Zeta.localizedIndex S n ∧
      Nat.card
          (Omega.Zeta.xi_localized_solenoid_multiplication_kernel_degree_kernelModel S n) =
        Omega.Zeta.localizedIndex S n := by
  have hkernel :=
    (paper_xi_localized_solenoid_finite_subgroups_are_kernels S n hn).2
  exact ⟨rfl, hkernel⟩

end Omega.Zeta
