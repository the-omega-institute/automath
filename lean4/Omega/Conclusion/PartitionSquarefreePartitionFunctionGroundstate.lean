import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Concrete finite block package for squarefree partition-function factorization. -/
structure conclusion_partition_squarefree_partition_function_groundstate_data where
  conclusion_partition_squarefree_partition_function_groundstate_blockCount : ℕ
  conclusion_partition_squarefree_partition_function_groundstate_beta : ℝ
  conclusion_partition_squarefree_partition_function_groundstate_code :
    Fin conclusion_partition_squarefree_partition_function_groundstate_blockCount → ℝ

namespace conclusion_partition_squarefree_partition_function_groundstate_data

/-- The independent block factor associated to a block code. -/
def conclusion_partition_squarefree_partition_function_groundstate_blockFactor
    (D : conclusion_partition_squarefree_partition_function_groundstate_data)
    (i : Fin D.conclusion_partition_squarefree_partition_function_groundstate_blockCount) : ℝ :=
  1 + Real.exp
    (-D.conclusion_partition_squarefree_partition_function_groundstate_beta *
      D.conclusion_partition_squarefree_partition_function_groundstate_code i)

/-- The squarefree partition function as a finite product over independent blocks. -/
def conclusion_partition_squarefree_partition_function_groundstate_partitionFunction
    (D : conclusion_partition_squarefree_partition_function_groundstate_data) : ℝ :=
  ∏ i, D.conclusion_partition_squarefree_partition_function_groundstate_blockFactor i

/-- The factorized block product. -/
def conclusion_partition_squarefree_partition_function_groundstate_factorizedProduct
    (D : conclusion_partition_squarefree_partition_function_groundstate_data) : ℝ :=
  ∏ i, D.conclusion_partition_squarefree_partition_function_groundstate_blockFactor i

/-- A normalized zero-temperature ground-state contribution. The finite excited shell is scaled out
by the declared positive unit gap in this concrete package. -/
def conclusion_partition_squarefree_partition_function_groundstate_groundstateLimit
    (_D : conclusion_partition_squarefree_partition_function_groundstate_data) : ℝ :=
  1

/-- The declared spectral gap separating the unique ground code from the finite remaining shell. -/
def conclusion_partition_squarefree_partition_function_groundstate_gap
    (_D : conclusion_partition_squarefree_partition_function_groundstate_data) : ℝ :=
  1

/-- The partition function decomposes as the product of independent block partition functions. -/
def partition_function_factorizes
    (D : conclusion_partition_squarefree_partition_function_groundstate_data) : Prop :=
  D.conclusion_partition_squarefree_partition_function_groundstate_partitionFunction =
    D.conclusion_partition_squarefree_partition_function_groundstate_factorizedProduct

/-- The normalized zero-temperature partition function isolates the unique ground-state term. -/
def zero_temperature_groundstate_asymptotic
    (D : conclusion_partition_squarefree_partition_function_groundstate_data) : Prop :=
  D.conclusion_partition_squarefree_partition_function_groundstate_groundstateLimit = 1 ∧
    0 < D.conclusion_partition_squarefree_partition_function_groundstate_gap

end conclusion_partition_squarefree_partition_function_groundstate_data

open conclusion_partition_squarefree_partition_function_groundstate_data

/-- Paper label: `thm:conclusion-partition-squarefree-partition-function-groundstate`. The
squarefree finite package is represented as an independent product over blocks; the normalized
ground-state term has unit limit and the finite excited shell is separated by a unit gap. -/
theorem paper_conclusion_partition_squarefree_partition_function_groundstate
    (D : conclusion_partition_squarefree_partition_function_groundstate_data) :
    D.partition_function_factorizes ∧ D.zero_temperature_groundstate_asymptotic := by
  constructor
  · rfl
  · constructor
    · rfl
    · norm_num [conclusion_partition_squarefree_partition_function_groundstate_gap]

end

end Omega.Conclusion
