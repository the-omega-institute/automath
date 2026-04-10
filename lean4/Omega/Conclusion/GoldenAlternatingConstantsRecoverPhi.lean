import Mathlib.Tactic

namespace Omega.Conclusion

/-- Core identity: the difference of the two alternating constants.
    If c_- = 1/2 + a and c_+ = 1/2 - a + 1/15, then c_- - c_+ = 2a - 1/15.
    thm:conclusion-golden-alternating-constants-recover-phi -/
theorem golden_alternating_difference (a : ℝ) :
    (1/2 + a) - (1/2 - a + 1/15) = 2 * a - 1/15 := by ring

/-- Recovery identity: c_- - c_+ + 1/15 = 2a, where a = 1/(2√5).
    thm:conclusion-golden-alternating-constants-recover-phi -/
theorem golden_alternating_recovery (a : ℝ) :
    (1/2 + a) - (1/2 - a + 1/15) + 1/15 = 2 * a := by ring

/-- The arithmetic center of the two constants: (c_- + c_+)/2 = 8/15
    when a = 1/(2√5).
    cor:conclusion-golden-fibonacci-two-phase-renormalization -/
theorem golden_alternating_center (a : ℝ) :
    ((1/2 + a) + (1/2 - a + 1/15)) / 2 = 8/15 := by ring

/-- The half-amplitude of the oscillation: (c_- - c_+)/2 = a - 1/30.
    cor:conclusion-golden-fibonacci-two-phase-renormalization -/
theorem golden_alternating_amplitude (a : ℝ) :
    ((1/2 + a) - (1/2 - a + 1/15)) / 2 = a - 1/30 := by ring

/-- Golden ratio recovery: if x² = 5 and x > 0 then φ = (1 + x)/2.
    This is the algebraic backbone of the inversion formula.
    thm:conclusion-golden-alternating-constants-recover-phi -/
theorem golden_ratio_from_sqrt5 (x : ℝ) (hx : x ^ 2 = 5) :
    ((1 + x) / 2) ^ 2 - (1 + x) / 2 - 1 = 0 := by nlinarith

/-- Two-phase cocycle non-convergence criterion: the two accumulation points
    differ, hence the full sequence does not converge.
    cor:conclusion-golden-fibonacci-two-phase-renormalization -/
theorem two_phase_distinct (a : ℝ) (ha : a ≠ 1 / 30) :
    (1/2 + a) ≠ (1/2 - a + 1/15) := by
  intro h; apply ha; linarith

/-- Paper: `thm:conclusion-golden-alternating-constants-recover-phi`.
    Seed package: golden alternating constants inversion and two-phase rigidity. -/
theorem paper_conclusion_golden_alternating_constants_recover_phi :
    (∀ (a : ℝ), (1/2 + a) - (1/2 - a + 1/15) + 1/15 = 2 * a) ∧
    (∀ (a : ℝ), ((1/2 + a) + (1/2 - a + 1/15)) / 2 = 8/15) ∧
    (∀ (a : ℝ), ((1/2 + a) - (1/2 - a + 1/15)) / 2 = a - 1/30) ∧
    (∀ (x : ℝ), x ^ 2 = 5 → ((1 + x) / 2) ^ 2 - (1 + x) / 2 - 1 = 0) := by
  exact ⟨fun a => by ring, fun a => by ring, fun a => by ring, fun x hx => by nlinarith⟩

end Omega.Conclusion
