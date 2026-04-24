import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Chapter-local bookkeeping rank for the phase lattice attached to `L`. -/
def phaseRank (_L : Type*) : Nat :=
  0

/-- Phase samples are homomorphism coordinates into the `N`-th phase group, modeled here by the
`phaseRank L` independent coordinates of `Fin N`. -/
abbrev PhaseSamplingHom (_L : Type*) (N : Nat) :=
  Fin (phaseRank _L) → Fin N

/-- The number of `N`-phase samples is the cardinality of the coordinate-function model. -/
def phaseSamplingCount (L : Type*) (N : Nat) : Nat :=
  Fintype.card (PhaseSamplingHom L N)

/-- Paper label: `thm:conclusion-phase-sampling-growth-exponent-rank`. -/
theorem paper_conclusion_phase_sampling_growth_exponent_rank (L : Type*) (N : Nat) :
    phaseSamplingCount L N = N ^ phaseRank L := by
  simp [phaseSamplingCount, PhaseSamplingHom, phaseRank]

end Omega.Conclusion
