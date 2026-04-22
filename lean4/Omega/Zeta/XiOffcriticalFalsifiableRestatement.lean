import Omega.Zeta.FourthRegisterDichotomy
import Omega.Zeta.OffcriticalVisibilityThresholdBitBudget
import Omega.Zeta.XiNullThreeWay
import Omega.Zeta.XiUniqueContinuousTransverseRegister

namespace Omega.Zeta

/-- Paper label: `prop:xi-offcritical-falsifiable-restatement`. An off-critical claim can be
packaged either by explicitly extending the mode axis with radial data and paying the visibility
budget, or by producing the semantic/protocol `NULL` witness; in either case the continuous
transverse information is forced to factor through the unique radial register. -/
theorem paper_xi_offcritical_falsifiable_restatement
    (register : ℝ × ℝ → ℝ)
    {γ δ ρ b L : ℝ} {s : ℂ}
    (hphase : ∀ radius phase₁ phase₂, register (radius, phase₁) = register (radius, phase₂))
    (hmono : StrictMono fun radius => register (radius, 0))
    (hδ : 0 < δ)
    (hdyad : 1 - ρ = (2 : ℝ) ^ (-b))
    (hvis : 1 - ρ ≤ appOffcriticalBoundaryDepth γ δ)
    (hL : 1 < L) (hs : s.re ≠ 1 / 2) :
    ((((xiFactorsThroughRadius register ∧ xiUniqueUpToMonotoneReparam register) ∧
          Real.log ((γ ^ 2 + (1 + δ) ^ 2) / (4 * δ)) ≤ b * Real.log 2) ∨
        (xiSemanticNullBranch L s ∧ xiProtocolNullBranch L s ∧ xiOffsetPwClosureNull L s)) ∧
      (xiFactorsThroughRadius register ∧ xiUniqueUpToMonotoneReparam register)) := by
  have hRegister := paper_xi_unique_continuous_transverse_register register hphase hmono
  have hBudget :=
    paper_xi_offcritical_visibility_threshold_bit_budget
      (γ := γ) (δ := δ) (ρ := ρ) (b := b) (L := L) (s := s) hδ hdyad hvis hL hs
  have hNull := paper_xi_offset_null_type_safety hL hs
  have hSplit :
      (s.re ≠ 1 / 2) →
        ((xiFactorsThroughRadius register ∧ xiUniqueUpToMonotoneReparam register) ∧
            Real.log ((γ ^ 2 + (1 + δ) ^ 2) / (4 * δ)) ≤ b * Real.log 2) ∨
          (xiSemanticNullBranch L s ∧ xiProtocolNullBranch L s ∧ xiOffsetPwClosureNull L s) := by
    intro _
    exact Or.inl ⟨hRegister, hBudget.1⟩
  have hNoThird :
      (s.re ≠ 1 / 2) →
        (xiFactorsThroughRadius register ∧ xiUniqueUpToMonotoneReparam register) := by
    intro _
    exact hRegister
  simpa [xiSemanticNullBranch, xiProtocolNullBranch] using
    paper_xi_fourth_register_dichotomy
      (offsliceAssertion := s.re ≠ 1 / 2)
      (explicitRadialExtension :=
        (xiFactorsThroughRadius register ∧ xiUniqueUpToMonotoneReparam register) ∧
          Real.log ((γ ^ 2 + (1 + δ) ^ 2) / (4 * δ)) ≤ b * Real.log 2)
      (nullWitness := xiSemanticNullBranch L s ∧ xiProtocolNullBranch L s ∧ xiOffsetPwClosureNull L s)
      (noThirdPath := xiFactorsThroughRadius register ∧ xiUniqueUpToMonotoneReparam register)
      hSplit hNoThird hs

end Omega.Zeta
