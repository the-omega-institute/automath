import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.LeyangEndpointPreimageCos2Spectrum

namespace Omega.Conclusion

open Omega.UnitCirclePhaseArithmetic

/-- Pair the indices `k` and `n - k` coming from the endpoint cosine-squared parametrization. -/
def singularRingEndpointPairIndices (n : Nat) : Finset Nat :=
  (Finset.Icc 1 (n - 1)).image (fun k => Nat.min k (n - k))

/-- The endpoint trace set for the `n`th Lee--Yang iterate. -/
def singularRingEndpointTraceSet (n : Nat) : Set ℂ :=
  {w | leyangFn n w = 1 ∨ leyangFn n w = -1}

/-- Concrete wrapper for the endpoint spectrum law, the distinct-point count coming from pairing
`k` with `n - k`, and the multiplicative nesting of endpoint preimages. -/
def ConclusionSingularRingEndpointPreimageTower (m n : Nat) : Prop :=
  LeyangEndpointPreimageCos2SpectrumLaw n ∧
    (singularRingEndpointPairIndices n).card = n / 2 ∧
    Set.preimage (leyangFn m) (singularRingEndpointTraceSet n) =
      singularRingEndpointTraceSet (m * n)

private theorem singularRingEndpointPairIndices_eq_Icc (n : Nat) (hn : 2 ≤ n) :
    singularRingEndpointPairIndices n = Finset.Icc 1 (n / 2) := by
  ext r
  constructor
  · intro hr
    rcases Finset.mem_image.mp hr with ⟨k, hk, hkr⟩
    rw [Finset.mem_Icc]
    rw [Finset.mem_Icc] at hk
    have hrk : r ≤ k := by
      rw [← hkr]
      exact Nat.min_le_left _ _
    have hrnk : r ≤ n - k := by
      rw [← hkr]
      exact Nat.min_le_right _ _
    constructor
    · have hkpos : 0 < k := by omega
      have hnkpos : 0 < n - k := by omega
      have hrpos : 0 < r := by
        rw [← hkr]
        by_cases hle : k ≤ n - k
        · simpa [Nat.min_eq_left hle] using hkpos
        · have hle' : n - k ≤ k := Nat.le_of_not_ge hle
          simpa [Nat.min_eq_right hle'] using hnkpos
      omega
    · have hdouble : 2 * r ≤ n := by
        have hsum : r + r ≤ k + (n - k) := add_le_add hrk hrnk
        have hkn : k ≤ n := by omega
        calc
          2 * r = r + r := by ring
          _ ≤ k + (n - k) := hsum
          _ = n := Nat.add_sub_of_le hkn
      omega
  · intro hr
    rw [Finset.mem_Icc] at hr
    refine Finset.mem_image.mpr ?_
    refine ⟨r, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      constructor
      · exact hr.1
      · omega
    · have hle : r ≤ n - r := by omega
      simp [Nat.min_eq_left hle]

private theorem singularRingEndpointPairIndices_card (n : Nat) (hn : 2 ≤ n) :
    (singularRingEndpointPairIndices n).card = n / 2 := by
  rw [singularRingEndpointPairIndices_eq_Icc n hn]
  have hIcc :
      Finset.Icc 1 (n / 2) = Finset.range (n / 2 + 1) \ ({0} : Finset Nat) := by
    ext r
    simp [Finset.mem_Icc, Finset.mem_range, Nat.succ_le_iff, Nat.pos_iff_ne_zero]
    constructor <;> intro h <;> exact ⟨h.2, h.1⟩
  rw [hIcc, Finset.range_sdiff_zero]
  simpa using
    Finset.card_image_of_injective (Finset.range (n / 2))
      (by
        intro a b hab
        exact Nat.succ.inj hab)

private theorem singularRingEndpointTraceSet_preimage_mul
    (m n : Nat) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    Set.preimage (leyangFn m) (singularRingEndpointTraceSet n) =
      singularRingEndpointTraceSet (m * n) := by
  have hcomp := (paper_leyang_chebyshev_semiconjugacy n m hn hm).2
  ext z
  have hcompz : leyangFn n (leyangFn m z) = leyangFn (m * n) z := by
    have := congrArg (fun f => f z) hcomp
    simpa [Function.comp, Nat.mul_comm] using this
  simp [singularRingEndpointTraceSet, Set.preimage, hcompz]

/-- The endpoint spectrum is the cosine-squared family, its distinct values are counted by the
`k ↔ n - k` pairing, and endpoint preimages compose multiplicatively.
    thm:conclusion-singular-ring-endpoint-preimage-tower -/
theorem paper_conclusion_singular_ring_endpoint_preimage_tower
    (m n : Nat) (hm : 1 ≤ m) (hn : 2 ≤ n) : ConclusionSingularRingEndpointPreimageTower m n := by
  have hn1 : 1 ≤ n := by omega
  refine ⟨paper_leyang_endpoint_preimage_cos2_spectrum n hn,
    singularRingEndpointPairIndices_card n hn,
    singularRingEndpointTraceSet_preimage_mul m n hm hn1⟩

end Omega.Conclusion
