import Omega.CircleDimension.PhaseSeparationPrecisionExponent

namespace Omega.CircleDimension.PhasePrecisionTradeoff

open Omega.CircleDimension.PhaseSeparationPrecisionExponent

/-- Paper-facing dyadic phase-precision tradeoff, repackaged from the finite bin-counting bound.
    thm:cdim-phase-precision-tradeoff -/
theorem paper_cdim_phase_precision_tradeoff {G : Type*} [Fintype G] (r d N b : ℕ)
    (hG : Fintype.card G = boxCard r N) :
    (∀ enc : G → Fin (dyadicPhaseBinCount d b), Function.Injective enc →
        boxCard r N ≤ dyadicPhaseBinCount d b ∧ Nat.clog 2 (boxCard r N) ≤ d * b) ∧
      (boxCard r N > dyadicPhaseBinCount d b →
        ∀ enc : G → Fin (dyadicPhaseBinCount d b), ¬ Function.Injective enc) := by
  simpa using (paper_cdim_phase_separation_precision_exponent (G := G) r d N b hG)

end Omega.CircleDimension.PhasePrecisionTradeoff
