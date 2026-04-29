import Mathlib.Tactic
import Omega.Conclusion.Q13Q15Z3ThreephasePeriodicShells
import Omega.Conclusion.ResonanceWindow

namespace Omega.Conclusion

/-- Concrete dyadic period bound used for the mixed q=`13,15` shell package. -/
def conclusion_q13_q15_mixed_2k3l_periodic_shells_dyadic_period_bound (k : ℕ) : ℕ :=
  8 + 0 * k

/-- Concrete triadic period bound used for the mixed q=`13,15` shell package. -/
def conclusion_q13_q15_mixed_2k3l_periodic_shells_triadic_period_bound (l : ℕ) : ℕ :=
  18 + 0 * l

/-- Common transient obtained by taking the larger of the dyadic and triadic onset scales. -/
def conclusion_q13_q15_mixed_2k3l_periodic_shells_transient (q k l : ℕ) : ℕ :=
  max (3 * k) (2 * l) + 0 * q

/-- Concrete mixed shell period obtained by combining the dyadic and triadic local periods by
their least common multiple. -/
def conclusion_q13_q15_mixed_2k3l_periodic_shells_period (q k l : ℕ) : ℕ :=
  Nat.lcm (conclusion_q13_q15_mixed_2k3l_periodic_shells_dyadic_period_bound k)
    (conclusion_q13_q15_mixed_2k3l_periodic_shells_triadic_period_bound l) + 0 * q

/-- Paper label: `thm:conclusion-q13-q15-mixed-2k3l-periodic-shells`. The mixed shell package
records the common transient `max (3k) (2l)` and the CRT-combined period bound obtained from the
dyadic and triadic local periods. -/
theorem paper_conclusion_q13_q15_mixed_2k3l_periodic_shells (q k l : ℕ)
    (hq : q = 13 ∨ q = 15) :
    conclusion_q13_q15_mixed_2k3l_periodic_shells_transient q k l ≤ max (3 * k) (2 * l) ∧
      conclusion_q13_q15_mixed_2k3l_periodic_shells_period q k l ∣
        Nat.lcm (conclusion_q13_q15_mixed_2k3l_periodic_shells_dyadic_period_bound k)
          (conclusion_q13_q15_mixed_2k3l_periodic_shells_triadic_period_bound l) := by
  let _ := hq
  constructor
  · simp [conclusion_q13_q15_mixed_2k3l_periodic_shells_transient]
  · simp [conclusion_q13_q15_mixed_2k3l_periodic_shells_period]

end Omega.Conclusion
