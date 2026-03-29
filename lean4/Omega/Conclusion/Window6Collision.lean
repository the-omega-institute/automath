import Mathlib.Tactic

/-! ### Window-6 q-moment spectrum and collision probability

Arithmetic certificates for the conclusion chapter:
q-moment triple from histogram {2:8, 3:4, 4:9}, collision probability reduction,
and related Wedderburn dimension identities. -/

namespace Omega.Conclusion

-- ══════════════════════════════════════════════════════════════
-- Phase R130: Window-6 q-moment spectrum triple
-- ══════════════════════════════════════════════════════════════

/-- Window-6 q-moment spectrum from histogram {2:8, 3:4, 4:9}.
    S_0=21, S_1=64, S_2=212.
    thm:conclusion-window6-qmoment-triple-geometry -/
theorem window6_qmoment_triple :
    8 + 4 + 9 = 21 ∧
    8 * 2 + 4 * 3 + 9 * 4 = 64 ∧
    8 * 4 + 4 * 9 + 9 * 16 = 212 := by omega

/-- S_2(6) = Σ d(w)² = Wedderburn dimension 212.
    thm:conclusion-window6-qmoment-triple-geometry -/
theorem window6_S2_wedderburn :
    8 * 2 ^ 2 + 4 * 3 ^ 2 + 9 * 4 ^ 2 = 212 := by omega

/-- Likelihood ratio monotonicity: sector weights shift toward large fibers.
    thm:conclusion-window6-qmoment-triple-geometry -/
theorem window6_likelihood_shift :
    9 * 16 * 21 > 9 * 4 * 64 ∧ 9 * 4 * 21 > 9 * 1 * 64 := by omega

/-- Paper: thm:conclusion-window6-qmoment-triple-geometry -/
theorem paper_window6_qmoment_triple :
    8 + 4 + 9 = 21 ∧ 8 * 2 + 4 * 3 + 9 * 4 = 64 ∧ 8 * 4 + 4 * 9 + 9 * 16 = 212 :=
  window6_qmoment_triple

-- ══════════════════════════════════════════════════════════════
-- Phase R130: Window-6 collision probability rational form
-- ══════════════════════════════════════════════════════════════

/-- Collision probability fraction: 212/4096 = 53/1024.
    thm:conclusion-window6-groupoid-collision-dimension-identity -/
theorem window6_collision_prob_reduced :
    212 * 1024 = 53 * 4096 := by omega

/-- GCD reduction factor.
    thm:conclusion-window6-groupoid-collision-dimension-identity -/
theorem window6_collision_gcd : Nat.gcd 212 4096 = 4 := by native_decide

/-- Microstate count squared: 64² = 4096.
    thm:conclusion-window6-groupoid-collision-dimension-identity -/
theorem window6_microstate_sq : 64 ^ 2 = 4096 := by omega

/-- Reduced fraction components.
    thm:conclusion-window6-groupoid-collision-dimension-identity -/
theorem window6_collision_components :
    212 / 4 = 53 ∧ 4096 / 4 = 1024 := by omega

/-- Collision dimension exceeds 3× microstate count.
    thm:conclusion-window6-groupoid-collision-dimension-identity -/
theorem window6_collision_exceeds_linear : 212 > 3 * 64 := by omega

/-- Paper: thm:conclusion-window6-groupoid-collision-dimension-identity -/
theorem paper_window6_collision_prob :
    212 * 1024 = 53 * 4096 := window6_collision_prob_reduced

end Omega.Conclusion
