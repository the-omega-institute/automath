import Mathlib.Data.Real.Basic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9ob-escort-quantile-phase-diagram`. With the two strict
regime implications, the monotone critical curve, and the `q = 1` baseline provided explicitly,
the phase-diagram package is exactly their conjunction. -/
theorem paper_xi_time_part9ob_escort_quantile_phase_diagram
    (q epsilon epsilon_c : Real)
    (scaledLimitOne scaledLimitPhiInv criticalCurveStrictMono baselineQ1 : Prop)
    (hq : 0 ≤ q) (heps : 0 < epsilon ∧ epsilon < 1) (hneq : epsilon != epsilon_c)
    (hleft : epsilon < epsilon_c → scaledLimitOne)
    (hright : epsilon_c < epsilon → scaledLimitPhiInv)
    (hmono : criticalCurveStrictMono) (hbase : q = 1 → baselineQ1) :
    (epsilon < epsilon_c → scaledLimitOne) ∧
      (epsilon_c < epsilon → scaledLimitPhiInv) ∧
      criticalCurveStrictMono ∧
      (q = 1 → baselineQ1) := by
  have _ : 0 ≤ q := hq
  have _ : 0 < epsilon ∧ epsilon < 1 := heps
  have _ : epsilon != epsilon_c := hneq
  exact ⟨hleft, hright, hmono, hbase⟩

end Omega.Zeta
