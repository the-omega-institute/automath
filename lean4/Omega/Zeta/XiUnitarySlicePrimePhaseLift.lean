import Omega.Zeta.XiPrimePhaseTorusDenseUniquelyErgodic

namespace Omega.Zeta

/-- Paper-label wrapper for
`thm:xi-unitary-slice-prime-phase-lift-to-arithmetic-singular-ring`. -/
theorem paper_xi_unitary_slice_prime_phase_lift_to_arithmetic_singular_ring
    (L : ℕ) (hL : 2 ≤ L) :
    xi_prime_phase_torus_dense_uniquely_ergodic_statement L := by
  exact paper_xi_prime_phase_torus_dense_uniquely_ergodic L hL

end Omega.Zeta
