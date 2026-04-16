import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Chapter-local wrapper for the non-reset regeneration tail in the real-input-40 model. The
data package an abstract finite sub-Markov survival formula, a Perron-Frobenius/primitivity
certificate for the transient sector, and the resulting exponential tail estimate. -/
structure RealInput40ResetRegenerationTailData where
  survivalFormulaOnNonResetSector : Prop
  perronFrobeniusCertificate : Prop
  primitiveTransientSector : Prop
  tailFormula : Prop
  hasPerronRoot : Prop
  exponentialTailBound : Prop
  hasSurvivalFormulaOnNonResetSector : survivalFormulaOnNonResetSector
  hasPerronFrobeniusCertificate : perronFrobeniusCertificate
  hasPrimitiveTransientSector : primitiveTransientSector
  deriveTailFormula :
    survivalFormulaOnNonResetSector → tailFormula
  derivePerronRoot :
    perronFrobeniusCertificate → primitiveTransientSector → hasPerronRoot
  deriveExponentialTailBound :
    tailFormula → hasPerronRoot → exponentialTailBound

/-- Paper-facing wrapper for the real-input-40 reset-regeneration tail law.
    prop:real-input-40-reset-regeneration-tail -/
theorem paper_real_input_40_reset_regeneration_tail (D : RealInput40ResetRegenerationTailData) :
    D.tailFormula ∧ D.hasPerronRoot ∧ D.exponentialTailBound := by
  have hTail : D.tailFormula :=
    D.deriveTailFormula D.hasSurvivalFormulaOnNonResetSector
  have hPerron : D.hasPerronRoot :=
    D.derivePerronRoot D.hasPerronFrobeniusCertificate D.hasPrimitiveTransientSector
  exact ⟨hTail, hPerron, D.deriveExponentialTailBound hTail hPerron⟩

end Omega.SyncKernelWeighted
