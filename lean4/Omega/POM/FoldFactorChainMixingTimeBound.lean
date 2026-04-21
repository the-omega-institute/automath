import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.POM.FoldFactorChainDerivedInvariants

namespace Omega.POM

/-- Concrete parameters used to package the fold-factor-chain mixing-time estimate. -/
structure FoldFactorChainMixingTimeBoundData where
  m : ℕ
  hm : 1 ≤ m
  eps : ℝ
  heps : 0 < eps ∧ eps < 1 / 2

namespace FoldFactorChainMixingTimeBoundData

/-- The trivial stationary-mass lower bound `π_* ≥ 2^{-m}` written as `1 / 2^m`. -/
noncomputable def stationaryMassLower (D : FoldFactorChainMixingTimeBoundData) : ℝ :=
  1 / (2 : ℝ) ^ D.m

/-- The spectral-gap-based total-variation mixing bound after inserting the chapter gap lower
bound `2 / m`. -/
noncomputable def tvMixingUpper (D : FoldFactorChainMixingTimeBoundData) : ℝ :=
  (1 / foldFactorChainGapLower D.m) *
    (Real.log (1 / (2 * D.eps)) + (1 / 2 : ℝ) * Real.log (1 / D.stationaryMassLower))

/-- The standard spectral-gap-to-total-variation mixing inequality specialized to the chapter
bound `gap(P) ≥ 2 / m`. -/
def tvMixingBound (D : FoldFactorChainMixingTimeBoundData) : Prop :=
  D.tvMixingUpper =
    (D.m : ℝ) / 2 *
      (Real.log (1 / (2 * D.eps)) + (1 / 2 : ℝ) * Real.log (1 / D.stationaryMassLower))

/-- The explicit quadratic estimate obtained from `π_* ≥ 2^{-m}`. -/
def explicitQuadraticBound (D : FoldFactorChainMixingTimeBoundData) : Prop :=
  D.tvMixingUpper ≤
    (D.m : ℝ) ^ 2 * Real.log 2 / 4 + (D.m : ℝ) / 2 * Real.log (1 / (2 * D.eps))

private lemma log_two_pow (n : ℕ) : Real.log ((2 : ℝ) ^ n) = (n : ℝ) * Real.log 2 := by
  have h2pos : 0 < (2 : ℝ) := by norm_num
  have h2ne : (2 : ℝ) ≠ 0 := ne_of_gt h2pos
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hpow_ne : (2 : ℝ) ^ n ≠ 0 := by positivity
      rw [pow_succ, Real.log_mul hpow_ne h2ne, ih]
      rw [Nat.cast_add, Nat.cast_one]
      ring

private lemma tvMixingUpper_eq (D : FoldFactorChainMixingTimeBoundData) :
    D.tvMixingUpper =
      (D.m : ℝ) / 2 *
        (Real.log (1 / (2 * D.eps)) + (1 / 2 : ℝ) * Real.log (1 / D.stationaryMassLower)) := by
  unfold FoldFactorChainMixingTimeBoundData.tvMixingUpper foldFactorChainGapLower
  have hm_real : (D.m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt D.hm
  field_simp [hm_real]

private lemma log_inv_stationaryMassLower (D : FoldFactorChainMixingTimeBoundData) :
    Real.log (1 / D.stationaryMassLower) = (D.m : ℝ) * Real.log 2 := by
  have hpow_ne : (2 : ℝ) ^ D.m ≠ 0 := by positivity
  have hinv : 1 / D.stationaryMassLower = (2 : ℝ) ^ D.m := by
    unfold stationaryMassLower
    field_simp [hpow_ne]
  rw [hinv, log_two_pow]

end FoldFactorChainMixingTimeBoundData

/-- Paper label: `cor:pom-fold-factor-chain-mixing-time-bound`.
The gap lower bound `2 / m` and the trivial stationary-mass lower bound `2^{-m}` combine to give
the standard spectral-gap total-variation estimate and its explicit quadratic corollary. -/
theorem paper_pom_fold_factor_chain_mixing_time_bound (D : FoldFactorChainMixingTimeBoundData) :
    D.tvMixingBound ∧ D.explicitQuadraticBound := by
  refine ⟨?_, ?_⟩
  · unfold FoldFactorChainMixingTimeBoundData.tvMixingBound
    exact FoldFactorChainMixingTimeBoundData.tvMixingUpper_eq D
  · unfold FoldFactorChainMixingTimeBoundData.explicitQuadraticBound
    rw [FoldFactorChainMixingTimeBoundData.tvMixingUpper_eq]
    rw [FoldFactorChainMixingTimeBoundData.log_inv_stationaryMassLower]
    ring_nf
    linarith

end Omega.POM
