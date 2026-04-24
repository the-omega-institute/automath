import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Folding.BlockReservoirEncoding

namespace Omega.Folding

/-- A concrete reservoir-fiber packing obtained from the two constant base words when `k > 0`,
and from the unique empty word when `k = 0`. -/
def reservoirFiberPackingCode (k : ℕ) : Finset (List Bool) :=
  if _hk : 0 < k then
    {blockReservoirEncode (List.replicate k false), blockReservoirEncode (List.replicate k true)}
  else
    {blockReservoirEncode []}

/-- The normalized base-2 log-cardinality of the explicit reservoir packing family. -/
noncomputable def reservoirFiberPackingRate (k : ℕ) : ℝ :=
  Real.logb 2 ((reservoirFiberPackingCode k).card : ℝ) / (4 * (k + 1 : ℝ))

/-- Concrete finite-level packing package extracted from the block-reservoir construction:
every selected codeword lies in the reservoir fiber, distinct selected codewords have Hamming
distance at least `3 δ k`, the packing is nonempty, and its normalized log-cardinality is
nonnegative. -/
def reservoirFiberPackingStatement (k : ℕ) (δ : ℝ) : Prop :=
  let C := reservoirFiberPackingCode k
  (∀ ω ∈ C, blockReservoirFold ω = blockReservoirWord k) ∧
    (∀ ⦃ω ω' : List Bool⦄, ω ∈ C → ω' ∈ C → ω ≠ ω' →
      3 * δ * k ≤ blockReservoirHammingWeight (blockReservoirListXor ω ω')) ∧
    1 ≤ C.card ∧
    0 ≤ reservoirFiberPackingRate k

private lemma blockReservoirEncode_replicate_false_ne_true {k : ℕ} (hk : 0 < k) :
    blockReservoirEncode (List.replicate k false) ≠
      blockReservoirEncode (List.replicate k true) := by
  intro h
  have h' := blockReservoirEncode_injective h
  cases k with
  | zero =>
      cases hk.ne' rfl
  | succ n =>
      simp at h'

private lemma blockReservoirReplicate_distance_false_true (k : ℕ) :
    blockReservoirHammingWeight
        (blockReservoirListXor (blockReservoirEncode (List.replicate k false))
          (blockReservoirEncode (List.replicate k true))) =
      3 * k := by
  have hbase :
      blockReservoirHammingWeight
          (blockReservoirListXor (List.replicate k false) (List.replicate k true)) = k := by
    induction k with
    | zero =>
        simp [blockReservoirListXor, blockReservoirHammingWeight]
    | succ k ih =>
        simpa [List.replicate_succ, blockReservoirListXor, blockReservoirHammingWeight] using ih
  have hlen : (List.replicate k false).length = (List.replicate k true).length := by simp
  calc
    blockReservoirHammingWeight
        (blockReservoirListXor (blockReservoirEncode (List.replicate k false))
          (blockReservoirEncode (List.replicate k true))) =
      3 * blockReservoirHammingWeight
        (blockReservoirListXor (List.replicate k false) (List.replicate k true)) := by
        simpa using
          (blockReservoirHammingWeight_xor_encode (w := List.replicate k false)
            (w' := List.replicate k true) hlen)
    _ = 3 * k := by simp [hbase]

private lemma blockReservoirReplicate_distance_true_false (k : ℕ) :
    blockReservoirHammingWeight
        (blockReservoirListXor (blockReservoirEncode (List.replicate k true))
          (blockReservoirEncode (List.replicate k false))) =
      3 * k := by
  have hbase :
      blockReservoirHammingWeight
          (blockReservoirListXor (List.replicate k true) (List.replicate k false)) = k := by
    induction k with
    | zero =>
        simp [blockReservoirListXor, blockReservoirHammingWeight]
    | succ k ih =>
        simpa [List.replicate_succ, blockReservoirListXor, blockReservoirHammingWeight] using ih
  have hlen : (List.replicate k true).length = (List.replicate k false).length := by simp
  calc
    blockReservoirHammingWeight
        (blockReservoirListXor (blockReservoirEncode (List.replicate k true))
          (blockReservoirEncode (List.replicate k false))) =
      3 * blockReservoirHammingWeight
        (blockReservoirListXor (List.replicate k true) (List.replicate k false)) := by
        simpa using
          (blockReservoirHammingWeight_xor_encode (w := List.replicate k true)
            (w' := List.replicate k false) hlen)
    _ = 3 * k := by simp [hbase]

/-- The explicit constant-word packing sits inside the block-reservoir fiber and has uniform
relative Hamming separation after transport by the threefold-distance encoder.
    thm:fold-reservoir-fiber-constant-relative-distance-packing -/
theorem paper_fold_reservoir_fiber_constant_relative_distance_packing (k : ℕ) (δ : ℝ)
    (hδ0 : 0 < δ) (hδhalf : δ < 1 / 2) : reservoirFiberPackingStatement k δ := by
  unfold reservoirFiberPackingStatement
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ0
  by_cases hk : 0 < k
  · let ω0 := blockReservoirEncode (List.replicate k false)
    let ω1 := blockReservoirEncode (List.replicate k true)
    have hω_ne : ω0 ≠ ω1 := by
      dsimp [ω0, ω1]
      exact blockReservoirEncode_replicate_false_ne_true hk
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ω hω
      have hmem : ω = ω0 ∨ ω = ω1 := by
        simp [reservoirFiberPackingCode, hk] at hω
        exact hω
      rcases hmem with rfl | rfl
      · simp [ω0, blockReservoirFold_encode]
      · simp [ω1, blockReservoirFold_encode]
    · intro ω ω' hω hω' hneq
      have hmem : ω = ω0 ∨ ω = ω1 := by
        simp [reservoirFiberPackingCode, hk] at hω
        exact hω
      have hmem' : ω' = ω0 ∨ ω' = ω1 := by
        simp [reservoirFiberPackingCode, hk] at hω'
        exact hω'
      rcases hmem with rfl | rfl <;> rcases hmem' with rfl | rfl
      · contradiction
      · have hdist :
            (blockReservoirHammingWeight (blockReservoirListXor ω0 ω1) : ℝ) = 3 * k := by
            exact_mod_cast (by simpa [ω0, ω1] using blockReservoirReplicate_distance_false_true k)
        have hδ_le_one : δ ≤ 1 := by linarith
        have hk_nonneg : (0 : ℝ) ≤ k := by positivity
        rw [hdist]
        nlinarith
      · have hdist :
            (blockReservoirHammingWeight (blockReservoirListXor ω1 ω0) : ℝ) = 3 * k := by
            exact_mod_cast (by simpa [ω0, ω1] using blockReservoirReplicate_distance_true_false k)
        have hδ_le_one : δ ≤ 1 := by linarith
        have hk_nonneg : (0 : ℝ) ≤ k := by positivity
        rw [hdist]
        nlinarith
      · contradiction
    · simp [reservoirFiberPackingCode, hk]
    · have hlog_nonneg : 0 ≤ Real.logb 2 ((reservoirFiberPackingCode k).card : ℝ) := by
        simp [reservoirFiberPackingCode, hk]
        exact Real.logb_nonneg (by norm_num) (by norm_num)
      have hden_nonneg : 0 ≤ 4 * (k + 1 : ℝ) := by positivity
      exact div_nonneg hlog_nonneg hden_nonneg
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro ω hω
      have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
      simp [reservoirFiberPackingCode, hk] at hω
      subst hω
      simpa [hk0] using (blockReservoirFold_encode ([] : List Bool))
    · intro ω ω' hω hω' hneq
      simp [reservoirFiberPackingCode, hk] at hω hω'
      subst hω
      subst hω'
      contradiction
    · simp [reservoirFiberPackingCode, hk]
    · have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
      simp [reservoirFiberPackingRate, reservoirFiberPackingCode, hk0]

end Omega.Folding
