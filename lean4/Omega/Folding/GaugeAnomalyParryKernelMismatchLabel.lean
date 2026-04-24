import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyJordanFingerprint

namespace Omega.Folding

open Matrix
open scoped BigOperators

/-- The unweighted `4 × 4` adjacency matrix `M = 2 A₀` from the uniform gauge-anomaly model,
written in the state order `(a,b,c,d)`. -/
def foldGaugeAnomalyMismatchMatrix : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(1 : ℚ), 1, 0, 1;
    0, 0, 1, 0;
    1, 2, 0, 0;
    1, 0, 0, 0]

/-- The closed-form right Perron vector from the paper. -/
def foldGaugeAnomalyPerronVector : Fin 4 → ℚ :=
  ![(2 : ℚ), 1, 2, 1]

/-- The three mismatch-labelled edges from the uniform baseline. -/
def foldGaugeAnomalyMismatchLabel (i j : Fin 4) : ℕ :=
  if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then 1 else 0

/-- The uniform-baseline mismatch indicator read off from the three `e^θ` entries of `A_θ`. -/
def foldGaugeAnomalyUniformBaselineMismatchIndicator : Fin 4 → Fin 4 → ℕ :=
  !![(0 : ℕ), 1, 0, 0;
    0, 0, 1, 0;
    1, 0, 0, 0;
    0, 0, 0, 0]

/-- Paper-facing package for the Parry kernel and mismatch labels of the uniform
gauge-anomaly presentation. -/
def FoldGaugeAnomalyParryKernelMismatchLabel : Prop :=
  foldGaugeAnomalyMismatchMatrix.mulVec foldGaugeAnomalyPerronVector =
      (2 : ℚ) • foldGaugeAnomalyPerronVector ∧
    gaugeAnomalyJordanParryKernel =
      !![(1 / 2 : ℚ), (1 / 4 : ℚ), 0, (1 / 4 : ℚ);
        0, 0, 1, 0;
        (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0;
        1, 0, 0, 0] ∧
    (∀ i j,
      gaugeAnomalyJordanParryKernel i j =
        foldGaugeAnomalyMismatchMatrix i j * foldGaugeAnomalyPerronVector j /
          (2 * foldGaugeAnomalyPerronVector i)) ∧
    (∀ i j,
      foldGaugeAnomalyMismatchLabel i j = 1 ↔
        (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 0)) ∧
    (∀ i j,
      foldGaugeAnomalyMismatchLabel i j = foldGaugeAnomalyUniformBaselineMismatchIndicator i j)

private lemma foldGaugeAnomalyMismatchMatrix_mulVec :
    foldGaugeAnomalyMismatchMatrix.mulVec foldGaugeAnomalyPerronVector =
      (2 : ℚ) • foldGaugeAnomalyPerronVector := by
  native_decide

private lemma foldGaugeAnomalyParryKernel_formula (i j : Fin 4) :
    gaugeAnomalyJordanParryKernel i j =
      foldGaugeAnomalyMismatchMatrix i j * foldGaugeAnomalyPerronVector j /
        (2 * foldGaugeAnomalyPerronVector i) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [gaugeAnomalyJordanParryKernel, foldGaugeAnomalyMismatchMatrix,
      foldGaugeAnomalyPerronVector]

private lemma foldGaugeAnomalyMismatchLabel_spec (i j : Fin 4) :
    foldGaugeAnomalyMismatchLabel i j = 1 ↔
      (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 0) := by
  fin_cases i <;> fin_cases j <;> simp [foldGaugeAnomalyMismatchLabel]

private lemma foldGaugeAnomalyMismatchLabel_matchesUniform (i j : Fin 4) :
    foldGaugeAnomalyMismatchLabel i j = foldGaugeAnomalyUniformBaselineMismatchIndicator i j := by
  fin_cases i <;> fin_cases j <;>
    simp [foldGaugeAnomalyMismatchLabel, foldGaugeAnomalyUniformBaselineMismatchIndicator]

/-- The Parry-normalized kernel of the uniform gauge-anomaly graph is the explicit matrix from the
paper, the Perron vector is verified directly, and the three mismatch edges coincide with the
uniform-baseline mismatch indicator.
    prop:fold-gauge-anomaly-parry-kernel-mismatch-label -/
theorem paper_fold_gauge_anomaly_parry_kernel_mismatch_label :
    FoldGaugeAnomalyParryKernelMismatchLabel := by
  refine ⟨foldGaugeAnomalyMismatchMatrix_mulVec, rfl,
    foldGaugeAnomalyParryKernel_formula, foldGaugeAnomalyMismatchLabel_spec,
    foldGaugeAnomalyMismatchLabel_matchesUniform⟩

end Omega.Folding
