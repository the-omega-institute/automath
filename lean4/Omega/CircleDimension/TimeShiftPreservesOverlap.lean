import Mathlib.Tactic
import Omega.CircleDimension.DiscreteUnitaryEvolution

namespace Omega.CircleDimension

/-- Concrete time-shift wrapper for readable time words on the visible four-state quotient. -/
structure ReadableTimeWordTimeShiftData extends ReadableTimeWordUnitaryEvolutionData where
  visibleDistribution : Fin 4 → ℚ
  shift : Equiv.Perm (Fin 4)
  visibleDistributionInvariant : ∀ w, visibleDistribution (shift w) = visibleDistribution w

/-- The visible overlap pairing is the product of the visible distributions of the two words. -/
def ReadableTimeWordTimeShiftData.overlapPairing
    (D : ReadableTimeWordTimeShiftData) (u v : Fin 4) : ℚ :=
  D.visibleDistribution u * D.visibleDistribution v

/-- Synchronous time shift preserves the readable overlap kernel. -/
def ReadableTimeWordTimeShiftData.shiftPreservesOverlap
    (D : ReadableTimeWordTimeShiftData) : Prop :=
  ∀ u v, D.overlapPairing (D.shift u) (D.shift v) = D.overlapPairing u v

/-- Paper label: `prop:cdim-time-shift-preserves-overlap`. -/
theorem paper_cdim_time_shift_preserves_overlap (D : ReadableTimeWordTimeShiftData) :
    D.shiftPreservesOverlap := by
  intro u v
  dsimp [ReadableTimeWordTimeShiftData.shiftPreservesOverlap,
    ReadableTimeWordTimeShiftData.overlapPairing]
  rw [D.visibleDistributionInvariant u, D.visibleDistributionInvariant v]

end Omega.CircleDimension
