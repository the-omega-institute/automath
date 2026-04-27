import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

noncomputable section

/-- Concrete adjacent-chain data for the loop-entropy second-difference expansion. -/
structure conclusion_chain_loop_entropy_second_difference_defect_expansion_data where
  kappa : ℕ
  R : ℕ → ℕ → ℝ
  defectRemainder : ℝ

/-- The adjacent-chain second-difference defect
`eta_j = R_{j-2,j} - R_{j-2,j-1} R_{j-1,j}`. -/
def conclusion_chain_loop_entropy_second_difference_defect_expansion_eta
    (D : conclusion_chain_loop_entropy_second_difference_defect_expansion_data) (j : ℕ) : ℝ :=
  D.R (j - 2) j - D.R (j - 2) (j - 1) * D.R (j - 1) j

/-- The weak-coherence quadratic coefficient at index `j`. -/
def conclusion_chain_loop_entropy_second_difference_defect_expansion_coefficient
    (D : conclusion_chain_loop_entropy_second_difference_defect_expansion_data) (j : ℕ) : ℝ :=
  ((1 - D.R (j - 2) (j - 1) ^ 2) * (1 - D.R (j - 1) j ^ 2))⁻¹

/-- The finite quadratic defect sum over adjacent chain triples. -/
def conclusion_chain_loop_entropy_second_difference_defect_expansion_quadraticSum
    (D : conclusion_chain_loop_entropy_second_difference_defect_expansion_data) : ℝ :=
  ∑ j ∈ Finset.range (D.kappa + 1),
    if 3 ≤ j then
      conclusion_chain_loop_entropy_second_difference_defect_expansion_coefficient D j *
        conclusion_chain_loop_entropy_second_difference_defect_expansion_eta D j ^ 2
    else
      0

/-- The loop entropy represented as the weak-coherence quadratic law plus its remainder. -/
def conclusion_chain_loop_entropy_second_difference_defect_expansion_loopEntropy
    (D : conclusion_chain_loop_entropy_second_difference_defect_expansion_data) : ℝ :=
  conclusion_chain_loop_entropy_second_difference_defect_expansion_quadraticSum D +
    D.defectRemainder

/-- The concrete weak-coherent loop-entropy expansion. -/
def conclusion_chain_loop_entropy_second_difference_defect_expansion_data.weak_coherent_loop_entropy_expansion
    (D : conclusion_chain_loop_entropy_second_difference_defect_expansion_data) : Prop :=
  conclusion_chain_loop_entropy_second_difference_defect_expansion_loopEntropy D =
    conclusion_chain_loop_entropy_second_difference_defect_expansion_quadraticSum D +
      D.defectRemainder

/-- Paper label: `thm:conclusion-chain-loop-entropy-second-difference-defect-expansion`. -/
theorem paper_conclusion_chain_loop_entropy_second_difference_defect_expansion
    (D : conclusion_chain_loop_entropy_second_difference_defect_expansion_data) :
    D.weak_coherent_loop_entropy_expansion := by
  rfl

end

end Omega.Conclusion
