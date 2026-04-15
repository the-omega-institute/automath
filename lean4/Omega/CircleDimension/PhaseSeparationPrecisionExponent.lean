import Mathlib.Data.Nat.Log
import Mathlib.Data.Fin.Embedding
import Mathlib.Tactic

namespace Omega.CircleDimension.PhaseSeparationPrecisionExponent

/-- The cardinality of the radius-`N` box in rank `r`.
    thm:cdim-phase-separation-precision-exponent -/
def boxCard (r N : ℕ) : ℕ := (2 * N + 1) ^ r

/-- A uniform `L`-grid on `k` channels has `L^k` bins. -/
def gridBinCount (k L : ℕ) : ℕ := L ^ k

/-- A `b`-bit readout on each of `k` phase channels yields `2^(k b)` bins.
    thm:cdim-phase-separation-precision-exponent -/
def dyadicPhaseBinCount (k b : ℕ) : ℕ := 2 ^ (k * b)

/-- Any positive-dimensional grid can host `M` points once the side length reaches `M`. -/
private theorem exists_gridSide (k M : ℕ) (hk : 0 < k) :
    ∃ L, M ≤ gridBinCount k L := by
  by_cases hM : M = 0
  · subst hM
    exact ⟨0, Nat.zero_le _⟩
  · refine ⟨M, ?_⟩
    have hM1 : 1 ≤ M := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hM)
    simpa [gridBinCount] using
      (show M ^ 1 ≤ M ^ k from pow_le_pow_right' hM1 hk)

/-- The least grid side length whose `k`-channel cartesian grid can host `M` points. -/
noncomputable def minimalGridSide (k M : ℕ) (hk : 0 < k) : ℕ :=
  Nat.find (exists_gridSide k M hk)

theorem minimalGridSide_spec (k M : ℕ) (hk : 0 < k) :
    M ≤ gridBinCount k (minimalGridSide k M hk) :=
  Nat.find_spec (exists_gridSide k M hk)

theorem minimalGridSide_min {k M m : ℕ} (hk : 0 < k)
    (hm : M ≤ gridBinCount k m) :
    minimalGridSide k M hk ≤ m :=
  Nat.find_min' (exists_gridSide k M hk) hm

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

set_option maxHeartbeats 400000 in
/-- Explicit finite-grid recovery package: the least `k`-channel grid side length supporting the
box `(2N+1)^r` admits an injective code, while the previous side length does not. This squeezes the
box cardinality between consecutive `k`th powers, matching the `r / k` exponent at finite scale.
    prop:cdim-phase-separation-exponent-recovery -/
theorem paper_cdim_phase_separation_exponent_recovery
    {G : Type*} [Fintype G] (r k N : ℕ) (hk : 0 < k)
    (hG : Fintype.card G = boxCard r N) :
    let L := minimalGridSide k (boxCard r N) hk
    ∃ enc : G → Fin (gridBinCount k L),
      Function.Injective enc ∧
      gridBinCount k (L - 1) < boxCard r N ∧
      boxCard r N ≤ gridBinCount k L := by
  classical
  let L := minimalGridSide k (boxCard r N) hk
  have hL : boxCard r N ≤ gridBinCount k L :=
    minimalGridSide_spec k (boxCard r N) hk
  have hBoxPos : 0 < boxCard r N := by
    dsimp [boxCard]
    exact Nat.pow_pos (by omega : 0 < 2 * N + 1)
  have hLpos : 0 < L := by
    by_contra hLpos
    have hLzero : L = 0 := Nat.eq_zero_of_not_pos hLpos
    have hBoxZero : boxCard r N = 0 := by
      simpa [gridBinCount, hLzero, hk.ne'] using hL
    exact hBoxPos.ne' hBoxZero
  have hPrev : gridBinCount k (L - 1) < boxCard r N := by
    have hnot : ¬ boxCard r N ≤ gridBinCount k (L - 1) := by
      intro hPrevLe
      have hmin : L ≤ L - 1 :=
        minimalGridSide_min hk hPrevLe
      exact (Nat.not_le_of_gt (Nat.sub_lt hLpos (by decide : 0 < 1))) hmin
    exact lt_of_not_ge hnot
  let eG : G ≃ Fin (boxCard r N) :=
    (Fintype.equivFin G).trans (finCongr hG)
  refine ⟨fun x => Fin.castLE hL (eG x), ?_, hPrev, hL⟩
  intro x y hxy
  apply eG.injective
  exact (Fin.castLE_injective hL) hxy

end Omega.CircleDimension.PhaseSeparationPrecisionExponent
