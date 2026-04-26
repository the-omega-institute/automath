import Omega.CircleDimension.CoherenceTimeBarrier2Pow
import Omega.CircleDimension.CoherenceTimeLowerBoundMOneOverD

namespace Omega.CircleDimension

/-- Paper-facing `2^k` specialization of the coherence-time lower bound. Whenever the number of
readout classes stays below `2^k`, no injective encoding of `2^k` candidates exists. -/
def paper_cdim_coherence_time_barrier_2power_k_over_d_statement : Prop :=
  ∀ (C d t k p : ℕ),
    p ≤ C * t ^ d →
    p < 2 ^ k →
    ¬ ∃ f : Fin (2 ^ k) → Fin p, Function.Injective f

/-- Paper label: `cor:cdim-coherence-time-barrier-2power-k-over-d`. -/
theorem paper_cdim_coherence_time_barrier_2power_k_over_d :
    paper_cdim_coherence_time_barrier_2power_k_over_d_statement := by
  intro C d t k p hBound hSmall
  exact paper_cdim_coherence_time_lower_bound_m_1overd (M := 2 ^ k) C d t p hBound hSmall

end Omega.CircleDimension
