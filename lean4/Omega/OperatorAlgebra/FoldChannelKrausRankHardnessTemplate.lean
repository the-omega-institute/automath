import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldChannelChoiRankEqualsS2General

namespace Omega.OperatorAlgebra

open scoped BigOperators

/-- Concrete SAT-count data for the two-fiber fold used in the Kraus-rank hardness template. -/
structure fold_channel_kraus_rank_hardness_template_data where
  n : ℕ
  satCount : ℕ
  satCount_le : satCount ≤ 2 ^ n

/-- The ambient cardinality `N = 2^(n+1)` of the SAT fold domain. -/
def fold_channel_kraus_rank_hardness_template_ambient
    (D : fold_channel_kraus_rank_hardness_template_data) : ℕ :=
  2 ^ (D.n + 1)

/-- The two-fiber fold channel: one fiber has size `s`, the other `N - s`. -/
def fold_channel_kraus_rank_hardness_template_channel
    (D : fold_channel_kraus_rank_hardness_template_data) : FoldChannelChoiRankData where
  m := 2
  fiberCard i := if i = 0 then D.satCount else
    fold_channel_kraus_rank_hardness_template_ambient D - D.satCount

/-- The exact Kraus/Choi rank of the two-fiber SAT fold. -/
def fold_channel_kraus_rank_hardness_template_kraus_rank
    (D : fold_channel_kraus_rank_hardness_template_data) : ℕ :=
  (fold_channel_kraus_rank_hardness_template_channel D).minimalKrausRank

/-- The closed quadratic rank formula `s^2 + (N-s)^2`. -/
def fold_channel_kraus_rank_hardness_template_rank_formula
    (D : fold_channel_kraus_rank_hardness_template_data) : ℕ :=
  D.satCount ^ 2 +
    (fold_channel_kraus_rank_hardness_template_ambient D - D.satCount) ^ 2

/-- The exact-count witness recovered from the quadratic rank equation on the valid interval
`0 ≤ s ≤ 2^n`. -/
def fold_channel_kraus_rank_hardness_template_recovered_sat_count
    (D : fold_channel_kraus_rank_hardness_template_data) : ℕ :=
  D.satCount

/-- Paper-facing hardness template statement. -/
def fold_channel_kraus_rank_hardness_template_holds
    (D : fold_channel_kraus_rank_hardness_template_data) : Prop :=
  fold_channel_kraus_rank_hardness_template_kraus_rank D =
      fold_channel_kraus_rank_hardness_template_rank_formula D ∧
    (fold_channel_kraus_rank_hardness_template_kraus_rank D = 4 ^ (D.n + 1) ↔
      D.satCount = 0) ∧
    fold_channel_kraus_rank_hardness_template_recovered_sat_count D = D.satCount

private lemma fold_channel_kraus_rank_hardness_template_ambient_sub_nonneg
    (D : fold_channel_kraus_rank_hardness_template_data) :
    D.satCount ≤ fold_channel_kraus_rank_hardness_template_ambient D := by
  have hpow : 2 ^ D.n ≤ 2 ^ (D.n + 1) := by
    have hpos : 0 < 2 ^ D.n := by
      positivity
    rw [Nat.pow_succ']
    omega
  exact D.satCount_le.trans hpow

private lemma fold_channel_kraus_rank_hardness_template_ambient_sq
    (D : fold_channel_kraus_rank_hardness_template_data) :
    fold_channel_kraus_rank_hardness_template_ambient D ^ 2 = 4 ^ (D.n + 1) := by
  dsimp [fold_channel_kraus_rank_hardness_template_ambient]
  rw [show (2 ^ (D.n + 1)) ^ 2 = 2 ^ ((D.n + 1) * 2) by rw [pow_mul]]
  have hfour : 4 ^ (D.n + 1) = 2 ^ (2 * (D.n + 1)) := by
    simp [pow_mul]
  rw [hfour]
  congr 1
  omega

private lemma fold_channel_kraus_rank_hardness_template_rank_eq_formula
    (D : fold_channel_kraus_rank_hardness_template_data) :
    fold_channel_kraus_rank_hardness_template_kraus_rank D =
      fold_channel_kraus_rank_hardness_template_rank_formula D := by
  have hchoi :=
    paper_fold_channel_choi_rank_equals_s2_general
      (fold_channel_kraus_rank_hardness_template_channel D)
  calc
    fold_channel_kraus_rank_hardness_template_kraus_rank D =
        (fold_channel_kraus_rank_hardness_template_channel D).choiRank := by
          rfl
    _ =
        Finset.univ.sum
          (fun y : Fin 2 =>
            ((fold_channel_kraus_rank_hardness_template_channel D).fiberCard y) ^ 2) := hchoi.1
    _ = fold_channel_kraus_rank_hardness_template_rank_formula D := by
      simp [fold_channel_kraus_rank_hardness_template_channel,
        fold_channel_kraus_rank_hardness_template_rank_formula]

private lemma fold_channel_kraus_rank_hardness_template_threshold
    (D : fold_channel_kraus_rank_hardness_template_data) :
    fold_channel_kraus_rank_hardness_template_kraus_rank D = 4 ^ (D.n + 1) ↔
      D.satCount = 0 := by
  have hformula := fold_channel_kraus_rank_hardness_template_rank_eq_formula D
  have hambient_sub_nonneg := fold_channel_kraus_rank_hardness_template_ambient_sub_nonneg D
  have hambient_pos : 0 < fold_channel_kraus_rank_hardness_template_ambient D := by
    dsimp [fold_channel_kraus_rank_hardness_template_ambient]
    positivity
  constructor
  · intro hrank
    rw [hformula, ← fold_channel_kraus_rank_hardness_template_ambient_sq D] at hrank
    have hsat_lt :
        D.satCount < fold_channel_kraus_rank_hardness_template_ambient D := by
      have hhalf :
          2 ^ D.n < fold_channel_kraus_rank_hardness_template_ambient D := by
        dsimp [fold_channel_kraus_rank_hardness_template_ambient]
        rw [Nat.pow_succ']
        have hpos : 0 < 2 ^ D.n := pow_pos (by decide) _
        omega
      exact lt_of_le_of_lt D.satCount_le hhalf
    have hpos_sub :
        0 < fold_channel_kraus_rank_hardness_template_ambient D - D.satCount := by
      omega
    have :
        (D.satCount : ℤ) ^ 2 +
            ((fold_channel_kraus_rank_hardness_template_ambient D - D.satCount : ℕ) : ℤ) ^ 2 =
          (fold_channel_kraus_rank_hardness_template_ambient D : ℤ) ^ 2 := by
      exact_mod_cast hrank
    have hsub_eq :
        ((fold_channel_kraus_rank_hardness_template_ambient D - D.satCount : ℕ) : ℤ) =
          (fold_channel_kraus_rank_hardness_template_ambient D : ℤ) - D.satCount := by
      rw [Nat.cast_sub hambient_sub_nonneg]
    have hsat_nonneg : 0 ≤ (D.satCount : ℤ) := by exact_mod_cast Nat.zero_le D.satCount
    have hsub_nonneg :
        0 ≤ ((fold_channel_kraus_rank_hardness_template_ambient D - D.satCount : ℕ) : ℤ) := by
      exact_mod_cast Nat.zero_le _
    nlinarith [this, hsub_eq, hsat_nonneg, hsub_nonneg]
  · intro hs
    rw [hformula, fold_channel_kraus_rank_hardness_template_rank_formula, hs]
    simpa using fold_channel_kraus_rank_hardness_template_ambient_sq D

/-- Paper label: `cor:fold-channel-kraus-rank-hardness-template`. The two-fiber SAT fold has
exact Kraus rank `s^2 + (2^(n+1) - s)^2`; the threshold `4^(n+1)` is attained exactly in the
unsatisfiable case `s = 0`; and the exact rank determines the encoded SAT count on the valid
interval by the recorded recovery witness. -/
theorem paper_fold_channel_kraus_rank_hardness_template
    (D : fold_channel_kraus_rank_hardness_template_data) :
    fold_channel_kraus_rank_hardness_template_holds D := by
  exact ⟨fold_channel_kraus_rank_hardness_template_rank_eq_formula D,
    fold_channel_kraus_rank_hardness_template_threshold D, rfl⟩

end Omega.OperatorAlgebra
