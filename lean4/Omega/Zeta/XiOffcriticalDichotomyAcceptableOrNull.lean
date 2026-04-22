import Omega.Zeta.XiNullCompleteTrichotomyOffline
import Omega.Zeta.XiOffcriticalFalsifiableRestatement
import Omega.Zeta.XiPwNoContinuousHair

namespace Omega.Zeta

/-- The offline `NULL` witness package attached to the exhaustive trichotomy. -/
def xiOfflineNullWitness
    (h : Omega.TypedAddressBiaxialCompletion.TypedAddressNullTrichotomyData) : Prop :=
  h.exhaustive ∧ h.semanticFailuresRequireAddressChange ∧
    h.protocolFailuresNeedProtocolRepair ∧ h.collisionFailuresNeedSupportAxisBudget

/-- Off-critical claims either admit the explicit acceptable radial extension with the sharp
visibility budget, or they collapse to the protocol `NULL` branch together with an offline witness;
the only continuous extra coordinate allowed in either case is the unique radial one. -/
def xiOffcriticalDichotomyAcceptableOrNullStatement : Prop :=
  ∀ (h : Omega.TypedAddressBiaxialCompletion.TypedAddressNullTrichotomyData)
      (D : XiPwTypeSafetyNullData) (register : ℝ × ℝ → ℝ)
      {γ δ ρ b L : ℝ} {s : ℂ},
    (∀ radius phase₁ phase₂, register (radius, phase₁) = register (radius, phase₂)) →
    StrictMono (fun radius => register (radius, 0)) →
    0 < δ →
    1 - ρ = (2 : ℝ) ^ (-b) →
    1 - ρ ≤ appOffcriticalBoundaryDepth γ δ →
    1 < L →
    s.re ≠ 1 / 2 →
    let acceptable :=
      ((xiFactorsThroughRadius register ∧ xiUniqueUpToMonotoneReparam register) ∧
        Real.log ((γ ^ 2 + (1 + δ) ^ 2) / (4 * δ)) ≤ b * Real.log 2)
    let nullBranch :=
      xiSemanticNullBranch L s ∧ xiProtocolNullBranch L s ∧ xiOffsetPwClosureNull L s ∧
        xiOfflineNullWitness h
    let noHair :=
      (D.modeAxisCompleteness ↔ D.hankelRanksUniformlyBounded) ∧
        xiFactorsThroughRadius register ∧ xiUniqueUpToMonotoneReparam register
    (acceptable ∨ nullBranch) ∧ noHair

theorem paper_xi_offcritical_dichotomy_acceptable_or_null :
    xiOffcriticalDichotomyAcceptableOrNullStatement := by
  intro h D register γ δ ρ b L s hphase hmono hδ hdyad hvis hL hs
  have hRest :=
    paper_xi_offcritical_falsifiable_restatement register hphase hmono hδ hdyad hvis hL hs
  have hOffline : xiOfflineNullWitness h := paper_xi_null_complete_trichotomy_offline h
  have hNoHair := paper_xi_pw_no_continuous_hair D register hphase hmono
  rcases hRest with ⟨hBranch, _hUnique⟩
  refine ⟨?_, hNoHair⟩
  cases hBranch with
  | inl hAccept =>
      exact Or.inl hAccept
  | inr hNull =>
      exact Or.inr ⟨hNull.1, hNull.2.1, hNull.2.2, hOffline⟩

end Omega.Zeta
