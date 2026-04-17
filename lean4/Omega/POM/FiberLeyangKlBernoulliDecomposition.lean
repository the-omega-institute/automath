import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- The one-root Lee--Yang Bernoulli KL contribution written in the closed form used by the
fiberwise decomposition. -/
noncomputable def leyangRootBernoulliKl (α tp tq : ℝ) : ℝ :=
  (tp / (tp + α)) * Real.log (tp / tq) - Real.log ((α + tp) / (α + tq))

/-- Concrete finite data for the Lee--Yang root decomposition of a conditional KL observable. The
root list, its summed Bernoulli response, the log-partition gap, and the closed conditional-KL
expression are all stored explicitly. -/
structure POMFiberLeyangKlBernoulliDecompositionData where
  rootCount : ℕ
  alpha : Fin rootCount → ℝ
  tp : ℝ
  tq : ℝ
  expectedResponse : ℝ
  logPartitionGap : ℝ
  conditionalKl : ℝ
  hExpectedResponse :
    expectedResponse = ∑ j, tp / (tp + alpha j)
  hLogPartitionGap :
    logPartitionGap = ∑ j, Real.log ((alpha j + tp) / (alpha j + tq))
  hConditionalKl :
    conditionalKl = expectedResponse * Real.log (tp / tq) - logPartitionGap

/-- The conditional KL observable equals the sum of the one-root Bernoulli KL closed forms. -/
def POMFiberLeyangKlBernoulliDecompositionData.klBernoulliDecomposition
    (D : POMFiberLeyangKlBernoulliDecompositionData) : Prop :=
  D.conditionalKl = ∑ j, leyangRootBernoulliKl (D.alpha j) D.tp D.tq

/-- Paper wrapper for the Lee--Yang rootwise Bernoulli KL decomposition.
    thm:pom-fiber-leyang-kl-bernoulli-decomposition -/
theorem paper_pom_fiber_leyang_kl_bernoulli_decomposition
    (D : POMFiberLeyangKlBernoulliDecompositionData) : D.klBernoulliDecomposition := by
  dsimp [POMFiberLeyangKlBernoulliDecompositionData.klBernoulliDecomposition,
    leyangRootBernoulliKl]
  rw [D.hConditionalKl, D.hExpectedResponse, D.hLogPartitionGap]
  calc
    (∑ j, D.tp / (D.tp + D.alpha j)) * Real.log (D.tp / D.tq) -
        ∑ j, Real.log ((D.alpha j + D.tp) / (D.alpha j + D.tq)) =
      (∑ j, (D.tp / (D.tp + D.alpha j)) * Real.log (D.tp / D.tq)) -
        ∑ j, Real.log ((D.alpha j + D.tp) / (D.alpha j + D.tq)) := by
          rw [← Finset.sum_mul]
    _ = ∑ j, ((D.tp / (D.tp + D.alpha j)) * Real.log (D.tp / D.tq) -
        Real.log ((D.alpha j + D.tp) / (D.alpha j + D.tq))) := by
          rw [← Finset.sum_sub_distrib]
    _ = ∑ j, leyangRootBernoulliKl (D.alpha j) D.tp D.tq := by
          rfl

end Omega.POM
