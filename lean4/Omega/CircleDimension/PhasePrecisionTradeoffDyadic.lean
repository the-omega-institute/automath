import Omega.CircleDimension.PhaseSeparationPrecisionExponent

namespace Omega.CircleDimension

open Omega.CircleDimension.PhaseSeparationPrecisionExponent

/-- Paper-facing dyadic reformulation of the phase-separation precision bound: an injective code
    into `d` phase channels with `b` dyadic bits per channel forces the `Nat.clog` lower bound.
    cor:cdim-phase-precision-tradeoff-dyadic -/
theorem paper_cdim_phase_precision_tradeoff_dyadic {G : Type*} [Fintype G] (r d N b : ℕ)
    (hG : Fintype.card G = Omega.CircleDimension.PhaseSeparationPrecisionExponent.boxCard r N)
    (hEnc :
      ∃ enc : G → Fin (Omega.CircleDimension.PhaseSeparationPrecisionExponent.dyadicPhaseBinCount d b),
        Function.Injective enc) :
    Nat.clog 2 (Omega.CircleDimension.PhaseSeparationPrecisionExponent.boxCard r N) ≤ d * b := by
  rcases hEnc with ⟨enc, henc⟩
  exact
    (paper_cdim_phase_separation_precision_exponent (G := G) r d N b hG).1 enc henc |>.2

end Omega.CircleDimension
