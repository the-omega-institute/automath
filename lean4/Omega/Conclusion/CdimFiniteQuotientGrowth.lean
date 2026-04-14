import Omega.CircleDimension.PhaseSpectrumQuotient

namespace Omega.Conclusion

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: finite quotient growth is polynomial of degree `r` with a uniformly
    bounded torsion correction.
    thm:conclusion-cdim-finite-quotient-growth -/
theorem paper_conclusion_cdim_finite_quotient_growth_seeds (r t : Nat) (ht : 0 < t) :
    ∃ u : Nat → Nat,
      (∀ n, Omega.CircleDimension.phaseSpectrumCount r t n = n ^ r * u n) ∧
      (∀ n, u n ≤ t) := by
  refine ⟨fun n => Nat.gcd t n, ?_, ?_⟩
  · intro n
    simpa using Omega.CircleDimension.paper_cdim_phase_spectrum_quotient_seeds r t n
  · intro n
    exact Nat.gcd_le_left n ht

end Omega.Conclusion
