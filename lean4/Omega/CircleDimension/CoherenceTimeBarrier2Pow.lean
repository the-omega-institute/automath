import Mathlib.Tactic
import Omega.CircleDimension.CoherenceTimeLowerBound

namespace Omega.CircleDimension.CoherenceTimeBarrier2Pow

/-- Specialization to `M = 2^k`: collision is guaranteed when `|α| < 2^k`.
    cor:cdim-coherence-time-barrier-2power-k-over-d -/
theorem paper_cdim_coherence_time_barrier_2power
    (k : ℕ) {α : Type*} [DecidableEq α] [Fintype α]
    (hk : Fintype.card α < 2 ^ k) (f : Fin (2 ^ k) → α) :
    ∃ i j : Fin (2 ^ k), i ≠ j ∧ f i = f j :=
  CoherenceTimeLowerBound.paper_cdim_coherence_time_lower_bound hk f

end Omega.CircleDimension.CoherenceTimeBarrier2Pow
