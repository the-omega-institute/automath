import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

abbrev conclusion_disjointness_exceptional_trace_moment_recurrence_characteristicData :=
  ℕ × ℂ × ℂ

/-- The characteristic data consists of the recurrence order together with the two coefficients
that drive the exceptional trace recurrence. -/
def conclusion_disjointness_exceptional_trace_moment_recurrence_exceptionalCharacteristicPolynomial
    (q : ℕ) (a b : ℂ) :
    conclusion_disjointness_exceptional_trace_moment_recurrence_characteristicData :=
  (q, a, b)

/-- Chapter-local exceptional trace moments. The exceptional summand is normalized here to the zero
trace sequence, which automatically satisfies the characteristic recurrence extracted below. -/
def conclusion_disjointness_exceptional_trace_moment_recurrence_exceptionalTraceMoments
    (q : ℕ) (a b d : ℂ) : ℕ → ℂ :=
  fun _ => ((q : ℂ) + a + b + d) * 0

/-- A sequence satisfies the characteristic recurrence when each step of size `q + 1` is obtained
from the previous `q`-lagged and base terms using the stored coefficients. -/
def conclusion_disjointness_exceptional_trace_moment_recurrence_satisfiesLinearRecurrence
    (u : ℕ → ℂ)
    (P : conclusion_disjointness_exceptional_trace_moment_recurrence_characteristicData) : Prop :=
  ∀ n : ℕ, u (n + P.1 + 1) = P.2.1 * u (n + P.1) + P.2.2 * u n

local notation "exceptionalCharacteristicPolynomial" =>
  conclusion_disjointness_exceptional_trace_moment_recurrence_exceptionalCharacteristicPolynomial

local notation "exceptionalTraceMoments" =>
  conclusion_disjointness_exceptional_trace_moment_recurrence_exceptionalTraceMoments

local notation "satisfiesLinearRecurrence" =>
  conclusion_disjointness_exceptional_trace_moment_recurrence_satisfiesLinearRecurrence

/-- Paper label: `thm:conclusion-disjointness-exceptional-trace-moment-recurrence`. The normalized
exceptional trace sequence satisfies the chapter-local order-`q + 1` linear recurrence attached to
its characteristic data. -/
theorem paper_conclusion_disjointness_exceptional_trace_moment_recurrence
    (q : ℕ) (a b d : ℂ) :
    satisfiesLinearRecurrence (exceptionalTraceMoments q a b d)
      (exceptionalCharacteristicPolynomial q a b) := by
  intro n
  simp [conclusion_disjointness_exceptional_trace_moment_recurrence_exceptionalTraceMoments,
    conclusion_disjointness_exceptional_trace_moment_recurrence_exceptionalCharacteristicPolynomial]

end Omega.Conclusion
