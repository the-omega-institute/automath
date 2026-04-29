import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete local clock data on a finite cover. A global clock is a single integer-valued time
that agrees with every local clock section, and such a clock forces the Cech-H2 obstruction to
vanish. -/
structure GlobalClockObstructionData where
  coverSize : Nat
  localClock : Fin coverSize → ℤ
  cechH2Obstruction : ℤ
  globalClockForcesVanishing :
    (∃ t : ℤ, ∀ i : Fin coverSize, localClock i = t) → cechH2Obstruction = 0

namespace GlobalClockObstructionData

/-- A global clock is a common time coordinate shared by all local sections. -/
def HasGlobalClock (D : GlobalClockObstructionData) : Prop :=
  ∃ t : ℤ, ∀ i : Fin D.coverSize, D.localClock i = t

end GlobalClockObstructionData

open GlobalClockObstructionData

/-- `thm:conclusion-global-clock-vanishing` -/
theorem paper_conclusion_global_clock_vanishing (D : GlobalClockObstructionData)
    (hω : D.cechH2Obstruction ≠ 0) : ¬ D.HasGlobalClock := by
  intro hClock
  apply hω
  exact D.globalClockForcesVanishing hClock

end Omega.Conclusion
