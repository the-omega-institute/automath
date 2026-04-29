import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-stokes-extension-phase-sampling-bound`. -/
theorem paper_conclusion_stokes_extension_phase_sampling_bound (Sigma : Nat -> Nat)
    (rank b : Nat) (hSigma : forall N, Sigma N = N ^ rank) (hrank : 2 * rank <= b) :
    forall N : Nat, 1 <= N -> (Sigma N) ^ 2 <= N ^ b := by
  intro N hN
  calc
    (Sigma N) ^ 2 = (N ^ rank) ^ 2 := by rw [hSigma N]
    _ = N ^ (rank * 2) := by rw [Nat.pow_mul]
    _ = N ^ (2 * rank) := by rw [Nat.mul_comm rank 2]
    _ <= N ^ b := Nat.pow_le_pow_right hN hrank

end Omega.Conclusion
