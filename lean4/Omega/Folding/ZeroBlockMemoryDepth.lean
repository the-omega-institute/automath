import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic
import Omega.Core.Fib
import Omega.Folding.ZeroBlockMinimaxAbsError

namespace Omega.Folding

private noncomputable def zeroBlockError (n : ℕ) : ℝ :=
  (1 : ℝ) / (4 * (Nat.fib (n + 3) : ℝ) * Nat.fib (n + 4))

/-- A linear lower bound that is sufficient to extract an explicit eventual depth threshold from
the exact zero-block minimax formula. -/
private theorem succ_le_fib_add_three : ∀ n : ℕ, n + 1 ≤ Nat.fib (n + 3)
  | 0 => by native_decide
  | n + 1 => by
      have ih : n + 1 ≤ Nat.fib (n + 3) := succ_le_fib_add_three n
      have hrec : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := by
        rw [show n + 4 = (n + 2) + 2 by omega, Nat.fib_add_two]
      have hpos : 1 ≤ Nat.fib (n + 2) := by
        exact Omega.one_le_fib_succ (n + 1)
      have hsum : n + 2 ≤ Nat.fib (n + 2) + Nat.fib (n + 3) := by omega
      simpa [hrec, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsum

private theorem zeroBlockError_antitone {n m : ℕ} (hnm : n ≤ m) :
    zeroBlockError m ≤ zeroBlockError n := by
  have hfib1 : Nat.fib (n + 3) ≤ Nat.fib (m + 3) := Nat.fib_mono (by omega)
  have hfib2 : Nat.fib (n + 4) ≤ Nat.fib (m + 4) := Nat.fib_mono (by omega)
  have hprod_nat :
      4 * Nat.fib (n + 3) * Nat.fib (n + 4) ≤ 4 * Nat.fib (m + 3) * Nat.fib (m + 4) := by
    gcongr
  have hprod :
      4 * (Nat.fib (n + 3) : ℝ) * Nat.fib (n + 4) ≤
        4 * (Nat.fib (m + 3) : ℝ) * Nat.fib (m + 4) := by
    exact_mod_cast hprod_nat
  have hfib3 : 0 < (Nat.fib (n + 3) : ℝ) := by
    exact_mod_cast Nat.fib_pos.mpr (by omega)
  have hfib4 : 0 < (Nat.fib (n + 4) : ℝ) := by
    exact_mod_cast Nat.fib_pos.mpr (by omega)
  have hpos : 0 < 4 * (Nat.fib (n + 3) : ℝ) * Nat.fib (n + 4) := by
    nlinarith
  exact one_div_le_one_div_of_le hpos hprod

private theorem exists_zeroBlockError_le (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, zeroBlockError n ≤ ε := by
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < 4 * ε by positivity)
  refine ⟨m, ?_⟩
  have hlin : (m + 1 : ℝ) ≤ (Nat.fib (m + 3) : ℝ) := by
    exact_mod_cast succ_le_fib_add_three m
  have hone : (1 : ℝ) ≤ (Nat.fib (m + 4) : ℝ) := by
    exact_mod_cast Omega.one_le_fib_succ (m + 3)
  have hden :
      (4 : ℝ) * (m + 1 : ℝ) ≤ 4 * (Nat.fib (m + 3) : ℝ) * Nat.fib (m + 4) := by
    have hmul : (Nat.fib (m + 3) : ℝ) ≤ (Nat.fib (m + 3) : ℝ) * Nat.fib (m + 4) := by
      nlinarith
    calc
      (4 : ℝ) * (m + 1 : ℝ) ≤ (4 : ℝ) * (Nat.fib (m + 3) : ℝ) := by
        gcongr
      _ ≤ 4 * (Nat.fib (m + 3) : ℝ) * Nat.fib (m + 4) := by
        nlinarith
  have hm' : (1 : ℝ) / (4 * (m + 1 : ℝ)) < ε := by
    have hfour : (0 : ℝ) < 4 := by norm_num
    have hm'' : ((1 : ℝ) / (m + 1 : ℝ)) / 4 < ε := by
      exact (div_lt_iff₀ hfour).2 (by simpa [mul_comm] using hm)
    simpa [zeroBlockError, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hm''
  have hbase :
      zeroBlockError m ≤ (1 : ℝ) / (4 * (m + 1 : ℝ)) := by
    have hpos : 0 < (4 : ℝ) * (m + 1 : ℝ) := by positivity
    exact one_div_le_one_div_of_le hpos hden
  exact le_trans hbase (le_of_lt hm')

/-- The zero-block gauge-anomaly minimax error eventually stays below any positive tolerance, and
the exact depth threshold is the least depth where the closed formula
`1 / (4 * F_{n+3} * F_{n+4})` crosses that tolerance.
    cor:fold-gauge-anomaly-zero-block-memory-depth -/
theorem paper_fold_gauge_anomaly_zero_block_memory_depth (ε : ℝ) (hε : 0 < ε) :
    ∃ nε : ℕ, ∀ n : ℕ,
      nε ≤ n ↔ (1 : ℝ) / (4 * (Nat.fib (n + 3) : ℝ) * Nat.fib (n + 4)) ≤ ε := by
  let P : ℕ → Prop := fun n => zeroBlockError n ≤ ε
  have hP : ∃ n : ℕ, P n := exists_zeroBlockError_le ε hε
  refine ⟨Nat.find hP, ?_⟩
  intro n
  constructor
  · intro hn
    have hfind : P (Nat.find hP) := Nat.find_spec hP
    exact le_trans (zeroBlockError_antitone hn) hfind
  · intro hn
    exact Nat.find_min' hP hn

end Omega.Folding
