import Mathlib.Data.Nat.Log
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Conclusion.TimeWindowAsymptoticallyFullPhaseLaw

namespace Omega.Conclusion

/-- The `b`-bit time-window source `(ℤ/2^bℤ)^T` realized as a function type. -/
abbrev TimeWindowBitSource (T b : ℕ) := Fin T → ZMod (2 ^ b)

/-- The phase-state bank with `k` slots of `b` bits each. -/
abbrev TimeWindowPhaseState (k b : ℕ) := Fin (2 ^ (b * k))

/-- Cardinality of the `b`-bit time-window source. -/
theorem timeWindowBitSource_card (T b : ℕ) :
    Fintype.card (TimeWindowBitSource T b) = 2 ^ (b * T) := by
  simp [TimeWindowBitSource, ZMod.card, pow_mul]

/-- Injective time-window encodings force the residual ledger to absorb the missing phase volume.
    The same counting inequality yields the exact `clog₂` lower bound and the polynomial-budget
    corollaries used in the paper.
    thm:conclusion-time-window-cdim-ledger-lower-bound -/
theorem paper_conclusion_time_window_cdim_ledger_lower_bound
    (T b k C : ℕ) {R : Type*} [Fintype R]
    (hEnc :
      ∃ f : TimeWindowBitSource T b → TimeWindowPhaseState k b × R, Function.Injective f) :
    2 ^ (b * (T - k)) ≤ Fintype.card R ∧
      b * (T - k) ≤ Nat.clog 2 (Fintype.card R) ∧
      (Fintype.card R ≤ T ^ C → b * (T - k) ≤ Nat.clog 2 (T ^ C)) ∧
      (0 < b → 2 ≤ T → Fintype.card R ≤ T ^ C → Nat.clog 2 T ≤ b → T - k ≤ C) := by
  rcases hEnc with ⟨f, hf⟩
  have hcard :
      Fintype.card (TimeWindowBitSource T b) ≤ Fintype.card (TimeWindowPhaseState k b × R) :=
    Fintype.card_le_of_injective f hf
  have hineq : 2 ^ (b * T) ≤ 2 ^ (b * k) * Fintype.card R := by
    simpa [timeWindowBitSource_card, TimeWindowPhaseState, Fintype.card_prod, pow_mul] using hcard
  have hledger :
      2 ^ (b * (T - k)) ≤ Fintype.card R :=
    paper_conclusion_time_window_asymptotically_full_phase_law T b k (Fintype.card R) hineq
  have hclog :
      b * (T - k) ≤ Nat.clog 2 (Fintype.card R) := by
    have := Nat.clog_mono_right 2 hledger
    simpa [Nat.clog_pow 2 (b * (T - k)) (by omega)] using this
  refine ⟨hledger, hclog, ?_, ?_⟩
  · intro hpoly
    exact le_trans hclog (Nat.clog_mono_right 2 hpoly)
  · intro hb _hT hpoly hblog
    have hTk_clog : b * (T - k) ≤ Nat.clog 2 (T ^ C) := by
      exact le_trans hclog (Nat.clog_mono_right 2 hpoly)
    have hTpow : T ^ C ≤ 2 ^ (b * C) := by
      have hTle : T ≤ 2 ^ b := (Nat.clog_le_iff_le_pow (by omega)).1 hblog
      calc
        T ^ C ≤ (2 ^ b) ^ C := by gcongr
        _ = 2 ^ (b * C) := by rw [pow_mul]
    have hclogTC : Nat.clog 2 (T ^ C) ≤ b * C := Nat.clog_le_of_le_pow hTpow
    have hmul : b * (T - k) ≤ b * C := le_trans hTk_clog hclogTC
    exact Nat.le_of_mul_le_mul_left hmul hb

end Omega.Conclusion
