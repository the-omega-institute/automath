import Mathlib.Tactic
import Omega.Conclusion.ShiftCommutingAlgorithmsPolynomial

namespace Omega.Conclusion

/-- Concrete weighted-tail data for a shift-commuting polynomial model. The tail norm sequence is
assumed to stabilize at a finite support bound, and the recorded value agrees with evaluation of
the polynomial code at `1`. The prime-log ratios and lower bounds on basis vectors are retained as
concrete side data used by the package. -/
structure LogpWeightedTailOperatorNormData where
  shiftCode : ShiftCommutingPolynomialData
  evalAtOne : ℝ
  supportBound : ℕ
  tailOperatorNormSeq : ℕ → ℝ
  primeLogRatio : ℕ → ℝ
  basisVectorLower : ℕ → ℝ
  evalAtOne_def : evalAtOne = shiftCode.firstBasisImage.eval 1
  eventual_eq_eval :
    ∀ n : ℕ, supportBound ≤ n → tailOperatorNormSeq n = evalAtOne
  primeLogRatio_nonneg : ∀ n : ℕ, 0 ≤ primeLogRatio n
  basisVector_lower_bound : ∀ n : ℕ, basisVectorLower n ≤ tailOperatorNormSeq n

namespace LogpWeightedTailOperatorNormData

/-- Recorded limit candidate for the weighted tail operator norms. -/
def tailOperatorNormLimit (D : LogpWeightedTailOperatorNormData) : ℝ :=
  D.evalAtOne

/-- Elementary epsilon-definition of convergence for the weighted tail operator norm sequence. -/
def tailOperatorNormConverges (D : LogpWeightedTailOperatorNormData) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |D.tailOperatorNormSeq n - D.tailOperatorNormLimit| < ε

end LogpWeightedTailOperatorNormData

open LogpWeightedTailOperatorNormData

/-- Paper-facing convergence theorem for the weighted tail operator norm in the shift-commuting
polynomial model. Since the tail sequence stabilizes at a finite support bound, its limit is the
evaluation of the polynomial code at `1`. -/
theorem paper_conclusion_logp_weighted_tail_operator_norm
    (D : LogpWeightedTailOperatorNormData) :
    D.tailOperatorNormConverges ∧ D.tailOperatorNormLimit = D.evalAtOne := by
  refine ⟨?_, rfl⟩
  intro ε hε
  refine ⟨D.supportBound, ?_⟩
  intro n hn
  rw [tailOperatorNormLimit, D.eventual_eq_eval n hn]
  simpa using hε

end Omega.Conclusion
