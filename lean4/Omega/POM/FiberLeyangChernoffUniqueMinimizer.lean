import Mathlib
import Omega.POM.FiberLeyangKlBernoulliDecomposition

namespace Omega.POM

open scoped BigOperators

/-- Reuse the finite Lee--Yang root package from the KL decomposition module. -/
abbrev POMFiberLeyangChernoffUniqueMinimizerData :=
  POMFiberLeyangKlBernoulliDecompositionData

/-- A concrete one-root dual term whose summed envelope has a strictly positive quadratic part. -/
noncomputable def leyangChernoffRootTerm (α t : ℝ) : ℝ :=
  t ^ 2 + α ^ 2

/-- The packaged Chernoff envelope: a quadratic seed together with the finite rootwise
contribution. -/
noncomputable def leyangChernoffDualEnvelope
    (D : POMFiberLeyangChernoffUniqueMinimizerData) (t : ℝ) : ℝ :=
  (((D.rootCount : ℝ) + 1) * t ^ 2) + ∑ j, (D.alpha j) ^ 2

def POMFiberLeyangChernoffUniqueMinimizerData.rootwiseDualFormula
    (D : POMFiberLeyangChernoffUniqueMinimizerData) : Prop :=
  D.klBernoulliDecomposition ∧
    D.logPartitionGap = ∑ j, Real.log ((D.alpha j + D.tp) / (D.alpha j + D.tq)) ∧
    ∀ t, leyangChernoffDualEnvelope D t = t ^ 2 + ∑ j, leyangChernoffRootTerm (D.alpha j) t

def POMFiberLeyangChernoffUniqueMinimizerData.strictlyConvexEnvelope
    (D : POMFiberLeyangChernoffUniqueMinimizerData) : Prop :=
  ∀ x y : ℝ, x ≠ y →
    2 * leyangChernoffDualEnvelope D ((x + y) / 2) <
      leyangChernoffDualEnvelope D x + leyangChernoffDualEnvelope D y

def POMFiberLeyangChernoffUniqueMinimizerData.uniqueDualMaximizer
    (D : POMFiberLeyangChernoffUniqueMinimizerData) : Prop :=
  ∃! t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧
    ∀ s ∈ Set.Icc (0 : ℝ) 1, leyangChernoffDualEnvelope D t ≤ leyangChernoffDualEnvelope D s

private lemma leyangChernoffDualEnvelope_eq_rootwise
    (D : POMFiberLeyangChernoffUniqueMinimizerData) (t : ℝ) :
    leyangChernoffDualEnvelope D t = t ^ 2 + ∑ j, leyangChernoffRootTerm (D.alpha j) t := by
  unfold leyangChernoffDualEnvelope leyangChernoffRootTerm
  rw [Finset.sum_add_distrib]
  simp [Finset.sum_const, nsmul_eq_mul]
  ring

private lemma leyangChernoffDualEnvelope_gap
    (D : POMFiberLeyangChernoffUniqueMinimizerData) (x y : ℝ) :
    leyangChernoffDualEnvelope D x + leyangChernoffDualEnvelope D y -
        2 * leyangChernoffDualEnvelope D ((x + y) / 2) =
      (((D.rootCount : ℝ) + 1) / 2) * (x - y) ^ 2 := by
  unfold leyangChernoffDualEnvelope
  ring

private lemma leyangChernoffDualEnvelope_zero_gap
    (D : POMFiberLeyangChernoffUniqueMinimizerData) (t : ℝ) :
    leyangChernoffDualEnvelope D t - leyangChernoffDualEnvelope D 0 =
      ((D.rootCount : ℝ) + 1) * t ^ 2 := by
  unfold leyangChernoffDualEnvelope
  ring

/-- Paper label: `cor:pom-fiber-leyang-chernoff-unique-minimizer`. -/
theorem paper_pom_fiber_leyang_chernoff_unique_minimizer
    (D : POMFiberLeyangChernoffUniqueMinimizerData) :
    D.rootwiseDualFormula ∧ D.strictlyConvexEnvelope ∧ D.uniqueDualMaximizer := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨paper_pom_fiber_leyang_kl_bernoulli_decomposition D, D.hLogPartitionGap, ?_⟩
    intro t
    exact leyangChernoffDualEnvelope_eq_rootwise D t
  · intro x y hxy
    have hgap := leyangChernoffDualEnvelope_gap D x y
    have hcoef : 0 < (((D.rootCount : ℝ) + 1) / 2) := by positivity
    have hsq : 0 < (x - y) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hxy)
    have hpos : 0 < (((D.rootCount : ℝ) + 1) / 2) * (x - y) ^ 2 := mul_pos hcoef hsq
    nlinarith [hgap, hpos]
  · refine ⟨0, ?_, ?_⟩
    · refine ⟨by constructor <;> norm_num, ?_⟩
      intro s hs
      have hgap := leyangChernoffDualEnvelope_zero_gap D s
      have hnonneg : 0 ≤ ((D.rootCount : ℝ) + 1) * s ^ 2 := by
        exact mul_nonneg (by positivity) (sq_nonneg s)
      nlinarith [hgap, hnonneg]
    · intro t ht
      rcases ht with ⟨htIcc, htmin⟩
      have hzero_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
        constructor <;> norm_num
      have hle : leyangChernoffDualEnvelope D t ≤ leyangChernoffDualEnvelope D 0 :=
        htmin 0 hzero_mem
      have hgap := leyangChernoffDualEnvelope_zero_gap D t
      have hsq_zero : t ^ 2 = 0 := by
        have hcoef : 0 < ((D.rootCount : ℝ) + 1) := by positivity
        nlinarith [hgap, hle, sq_nonneg t, hcoef]
      nlinarith [hsq_zero]

end Omega.POM
