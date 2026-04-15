import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace Omega.CircleDimension.PhaseSeparationPrecisionExponent

/-- The cardinality of the radius-`N` box in rank `r`.
    thm:cdim-phase-separation-precision-exponent -/
def boxCard (r N : ℕ) : ℕ := (2 * N + 1) ^ r

/-- A `b`-bit readout on each of `k` phase channels yields `2^(k b)` bins.
    thm:cdim-phase-separation-precision-exponent -/
def dyadicPhaseBinCount (k b : ℕ) : ℕ := 2 ^ (k * b)

/-- Dyadic precision reformulation of phase separation:
an injective `k`-channel, `b`-bit phase code for a box of size `(2N+1)^r`
forces `(2N+1)^r ≤ 2^(k b)`, hence `clog₂((2N+1)^r) ≤ k b`.
Equivalently, if the box cardinality exceeds the available bins, no such code
can be injective.
    thm:cdim-phase-separation-precision-exponent -/
theorem paper_cdim_phase_separation_precision_exponent :
    ∀ {G : Type*} [Fintype G] (r k N b : ℕ),
      Fintype.card G = boxCard r N →
      (∀ enc : G → Fin (dyadicPhaseBinCount k b), Function.Injective enc →
          boxCard r N ≤ dyadicPhaseBinCount k b ∧
          Nat.clog 2 (boxCard r N) ≤ k * b) ∧
      (boxCard r N > dyadicPhaseBinCount k b →
        ∀ enc : G → Fin (dyadicPhaseBinCount k b), ¬ Function.Injective enc) := by
  intro G _ r k N b hG
  constructor
  · intro enc hinj
    have hcard : Fintype.card G ≤ Fintype.card (Fin (dyadicPhaseBinCount k b)) :=
      Fintype.card_le_of_injective enc hinj
    have hbound : boxCard r N ≤ dyadicPhaseBinCount k b := by
      simpa [hG, boxCard, dyadicPhaseBinCount] using hcard
    refine ⟨hbound, ?_⟩
    exact (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2 (by
      simpa [dyadicPhaseBinCount] using hbound)
  · intro htooMany enc hinj
    exact Nat.not_le_of_gt htooMany <| by
      simpa [hG, boxCard, dyadicPhaseBinCount] using
        (Fintype.card_le_of_injective enc hinj)

end Omega.CircleDimension.PhaseSeparationPrecisionExponent
