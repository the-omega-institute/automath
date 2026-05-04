import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-phase-sampling-single-saturation-lagrangian`. -/
theorem paper_conclusion_phase_sampling_single_saturation_lagrangian
    (rank b N0 phaseCount : ℕ) (hN0 : 2 ≤ N0) (hFormula : phaseCount = N0 ^ rank)
    (hSat : phaseCount = N0 ^ (b / 2)) (_hHalf : 2 * rank ≤ b) (hEven : b % 2 = 0) :
    2 * rank = b := by
  have hrank : rank = b / 2 := by
    exact Nat.pow_right_injective hN0 (hFormula.symm.trans hSat)
  have hb : 2 * (b / 2) = b := by
    have h := Nat.div_add_mod b 2
    omega
  omega

end Omega.Conclusion
