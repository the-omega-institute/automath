import Mathlib.Tactic
import Omega.Zeta.AuditedEvenFirstCapacityKinkFibonacciJump
import Omega.Zeta.Window6MicrostateBiasedFiberlawHerglotzClosedform

namespace Omega.Zeta

/-- The explicit Fibonacci jump certified at the first audited-even capacity kink. -/
def xiFoldFibonacciCriticalResonanceGap : Real :=
  ((Nat.fib 4 : ℕ) : Real) - ((Nat.fib 3 : ℕ) : Real)

/-- The explicit size-biased max-fiber floor from the window-`6` model. -/
def xiFoldFibonacciMaxFiberBiasFloor : Real :=
  ((window6BiasedFiberMass 4 : ℚ) : Real)

/-- Mean-fiber normalization around the scalar parameter `Cphi`. -/
def xiFoldFibonacciMeanFiber (Cphi : Real) : Real :=
  Cphi

/-- Normalized collision gap obtained by adjoining the Fibonacci jump and the max-fiber bias
floor to the mean-fiber level. -/
def xiFoldFibonacciNormalizedGap (Cphi : Real) : Real :=
  xiFoldFibonacciMeanFiber Cphi +
    xiFoldFibonacciCriticalResonanceGap +
    xiFoldFibonacciMaxFiberBiasFloor

/-- Publication-facing positivity package for the normalized Fibonacci collision gap. -/
def XiFoldFibonacciCollisionGapPositiveFloor (Cphi : Real) : Prop :=
  0 < xiFoldFibonacciNormalizedGap Cphi - xiFoldFibonacciMeanFiber Cphi

/-- Paper label: `thm:xi-fold-fibonacci-collision-gap-positive-floor`. -/
theorem paper_xi_fold_fibonacci_collision_gap_positive_floor
    (Cphi : Real) : XiFoldFibonacciCollisionGapPositiveFloor Cphi := by
  have hjump_eq :
      xiFoldFibonacciCriticalResonanceGap = (Nat.fib 2 : Real) := by
    simpa [xiFoldFibonacciCriticalResonanceGap] using
      (paper_xi_audited_even_first_capacity_kink_fibonacci_jump 2).2.2
  have hjump_pos : 0 < xiFoldFibonacciCriticalResonanceGap := by
    rw [hjump_eq]
    norm_num [Nat.fib_add_two]
  have hbias_eq : xiFoldFibonacciMaxFiberBiasFloor = ((9 / 16 : ℚ) : Real) := by
    change ((window6BiasedFiberMass 4 : ℚ) : Real) = ((9 / 16 : ℚ) : Real)
    exact congrArg (fun q : ℚ => (q : Real))
      paper_xi_time_part9zc_window6_microstate_biased_fiberlaw_herglotz_closedform.2.2.1
  have hbias_pos : 0 < xiFoldFibonacciMaxFiberBiasFloor := by
    rw [hbias_eq]
    norm_num
  dsimp [XiFoldFibonacciCollisionGapPositiveFloor, xiFoldFibonacciNormalizedGap,
    xiFoldFibonacciMeanFiber]
  linarith

end Omega.Zeta
