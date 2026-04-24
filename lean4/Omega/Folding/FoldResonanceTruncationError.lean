import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

open scoped BigOperators
open scoped goldenRatio

namespace Omega.Folding

/-- The phase entering the fold-resonance cosine factor at depth `n`. -/
noncomputable def foldResonancePhase (u : ℝ) (n : ℕ) : ℝ :=
  Real.pi * u / Real.goldenRatio ^ n

/-- The cosine factor entering the fold-resonance product. -/
noncomputable def foldResonanceFactor (u : ℝ) (n : ℕ) : ℝ :=
  |Real.cos (foldResonancePhase u n)|

/-- The truncated product through depth `N`. -/
noncomputable def foldResonancePrefixProduct (u : ℝ) (N : ℕ) : ℝ :=
  Finset.prod (Finset.Icc 2 N) (fun n => foldResonanceFactor u n)

/-- A finite tail product used to control the truncation error after depth `N`. -/
noncomputable def foldResonanceTailProduct (u : ℝ) (N M : ℕ) : ℝ :=
  Finset.prod (Finset.Icc (N + 1) (N + M)) (fun n => foldResonanceFactor u n)

/-- The explicit exponential lower envelope obtained from the elementary pointwise estimate
`exp (-(phase^2)) ≤ |cos phase|` on the tail factors. -/
noncomputable def foldResonanceTailLowerProduct (u : ℝ) (N M : ℕ) : ℝ :=
  Finset.prod (Finset.Icc (N + 1) (N + M)) (fun n => Real.exp (-(foldResonancePhase u n) ^ 2))

/-- Concrete finite-window truncation bounds for the fold-resonance product. -/
noncomputable def foldResonanceTruncationErrorBounds (u : ℝ) (N M : ℕ) : Prop :=
  foldResonancePrefixProduct u N * foldResonanceTailLowerProduct u N M ≤
      foldResonancePrefixProduct u N * foldResonanceTailProduct u N M ∧
    foldResonancePrefixProduct u N * foldResonanceTailProduct u N M ≤
      foldResonancePrefixProduct u N

lemma foldResonanceFactor_nonneg (u : ℝ) (n : ℕ) : 0 ≤ foldResonanceFactor u n := by
  unfold foldResonanceFactor
  exact abs_nonneg _

lemma foldResonanceFactor_le_one (u : ℝ) (n : ℕ) : foldResonanceFactor u n ≤ 1 := by
  unfold foldResonanceFactor
  exact Real.abs_cos_le_one _

/-- Paper-facing finite truncation package for the fold-resonance cosine product: a pointwise
exponential lower bound on the tail factors gives a lower product bound, while `|cos x| ≤ 1`
controls the upper product bound.
    prop:fold-resonance-truncation-error -/
theorem paper_fold_resonance_truncation_error
    (u : ℝ) (N M : ℕ)
    (hlower : ∀ n ∈ Finset.Icc (N + 1) (N + M),
      Real.exp (-(foldResonancePhase u n) ^ 2) ≤ foldResonanceFactor u n) :
    foldResonanceTruncationErrorBounds u N M := by
  have hprefix_nonneg : 0 ≤ foldResonancePrefixProduct u N := by
    unfold foldResonancePrefixProduct
    refine Finset.prod_nonneg ?_
    intro n hn
    exact foldResonanceFactor_nonneg u n
  have htail_lower :
      foldResonanceTailLowerProduct u N M ≤ foldResonanceTailProduct u N M := by
    unfold foldResonanceTailLowerProduct foldResonanceTailProduct
    refine Finset.prod_le_prod ?_ ?_
    · intro n hn
      exact le_of_lt (Real.exp_pos _)
    · intro n hn
      exact hlower n hn
  have htail_le_one : foldResonanceTailProduct u N M ≤ 1 := by
    unfold foldResonanceTailProduct
    refine Finset.prod_le_one ?_ ?_
    · intro n hn
      exact foldResonanceFactor_nonneg u n
    · intro n hn
      exact foldResonanceFactor_le_one u n
  constructor
  · exact mul_le_mul_of_nonneg_left htail_lower hprefix_nonneg
  · calc
      foldResonancePrefixProduct u N * foldResonanceTailProduct u N M ≤
          foldResonancePrefixProduct u N * 1 := by
            exact mul_le_mul_of_nonneg_left htail_le_one hprefix_nonneg
      _ = foldResonancePrefixProduct u N := by ring

end Omega.Folding
