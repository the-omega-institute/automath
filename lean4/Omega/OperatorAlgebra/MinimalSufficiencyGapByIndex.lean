import Mathlib.Tactic
import Omega.OperatorAlgebra.CmiLowerBoundByIndexGap

namespace Omega.OperatorAlgebra

noncomputable section

/-- Scalar proxy for the minimal sufficiency gap statement: whenever the Jones index gap is
realized by a commuting-square configuration, every admissible recovery error is bounded below by
that gap, and a zero-error witness exists exactly in the zero-gap case. -/
def FoldMinimalSufficiencyGapByIndexStatement (Gamma : Real) : Prop :=
  ∀ ind1 ind2 ind12 : Real,
    0 < ind1 →
    0 < ind2 →
    0 < ind12 →
    ind12⁻¹ ≥ ind1⁻¹ * ind2⁻¹ →
    indexGap ind1 ind2 ind12 = Gamma →
      (∀ recoveryError : Real, indexGap ind1 ind2 ind12 ≤ recoveryError → Gamma ≤ recoveryError) ∧
      ((∃ recoveryError : Real,
          indexGap ind1 ind2 ind12 ≤ recoveryError ∧ recoveryError = 0) ↔
        Gamma = 0)

/-- Paper label: `prop:op-algebra-minimal-sufficiency-gap-by-index`.
The same index-gap obstruction that lower-bounds the delinking/CMI defect also lower-bounds every
scalar recovery-error proxy, and the equality case `Gamma = 0` is exactly the zero-error
recoverability regime. -/
theorem paper_op_algebra_minimal_sufficiency_gap_by_index
    (Gamma : Real) : FoldMinimalSufficiencyGapByIndexStatement Gamma := by
  intro ind1 ind2 ind12 h1 h2 h12 hcomp hGamma
  refine ⟨?_, ?_⟩
  · intro recoveryError hRecovery
    have hLower :=
      paper_op_algebra_cmi_lower_bound_by_index_gap h1 h2 h12 hcomp hRecovery
    simpa [hGamma] using hLower.1
  · constructor
    · rintro ⟨recoveryError, hRecovery, rfl⟩
      have hLower :=
        paper_op_algebra_cmi_lower_bound_by_index_gap h1 h2 h12 hcomp hRecovery
      have hZeroGap : indexGap ind1 ind2 ind12 = 0 := by
        linarith [hLower.2]
      simpa [hGamma] using hZeroGap
    · intro hGammaZero
      refine ⟨0, ?_, rfl⟩
      simp [hGamma, hGammaZero]

end

end Omega.OperatorAlgebra
