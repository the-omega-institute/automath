import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Conclusion.FrozenEscortTvRigidity
import Omega.POM.EscortMaxfiberTvBound

namespace Omega.POM

open Finset
open scoped BigOperators

/-- Binary entropy `h₂(t) = -t log t - (1 - t) log (1 - t)`. -/
private noncomputable def pomBinaryEntropy (t : ℝ) : ℝ :=
  -(t * Real.log t) - (1 - t) * Real.log (1 - t)

/-- Paper label: `thm:pom-finite-zero-temp-escort-uniform-maxfiber`.
This concrete wrapper combines the existing escort/max-fiber total-variation estimate with the
standard frozen-escort missing-mass identity, then records the usual `κ`-gap and entropy
decomposition consequences in terms of the off-maximal mass `ε`. -/
theorem paper_pom_finite_zero_temp_escort_uniform_maxfiber
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ) (fiberMultiplicity : α → ℕ) (Dm : ℕ)
    (maxFiber : Finset α) (escortLaw uniformLaw : α → ℝ)
    (tvDistance denominatorBound massOnMaxFiber exponentialGap : ℝ)
    (logM logN κ H ε remainder : ℝ)
    (hTvAsMissingMass :
      tvDistance =
        Finset.sum (offMaxFiberSubset fiberMultiplicity Dm)
          (fun x => escortWeight baseWeight fiberMultiplicity x))
    (hMissingMassLe :
      Finset.sum (offMaxFiberSubset fiberMultiplicity Dm)
          (fun x => escortWeight baseWeight fiberMultiplicity x) ≤
        denominatorBound)
    (hDenominatorLe : denominatorBound ≤ (Dm : ℝ) ^ (2 : ℕ))
    (hTvDef : tvDistance = Omega.Conclusion.frozenEscortL1Distance escortLaw uniformLaw)
    (hUniformOff : ∀ x, x ∉ maxFiber → uniformLaw x = 0)
    (hEscortEq : ∀ x, x ∈ maxFiber → escortLaw x = uniformLaw x)
    (hEscortNonneg : ∀ x, 0 ≤ escortLaw x)
    (hEscortTotal : Omega.Conclusion.frozenEscortTotalMass escortLaw = 1)
    (hMassOnMax :
      massOnMaxFiber = Omega.Conclusion.frozenEscortMassOnMaxFiber maxFiber escortLaw)
    (hGapBound : 1 - massOnMaxFiber ≤ Real.exp (-exponentialGap))
    (hε : ε = 1 - massOnMaxFiber)
    (hκ_nonneg : 0 ≤ logM - κ)
    (hκ_le : logM - κ ≤ logM * ε)
    (hEntropyDecomp : H = pomBinaryEntropy ε + (1 - ε) * logN + remainder)
    (hRemainder : remainder ≤ ε * logN) :
    tvDistance = 1 - massOnMaxFiber ∧
      tvDistance ≤ Real.exp (-exponentialGap) ∧
      tvDistance ≤ (Dm : ℝ) ^ (2 : ℕ) ∧
      0 ≤ logM - κ ∧
      logM - κ ≤ logM * tvDistance ∧
      H ≤ pomBinaryEntropy ε + logN := by
  let hEscort : EscortMaxfiberTvBoundData := {
    α := α
    instFintype := inferInstance
    instDecEq := inferInstance
    baseWeight := baseWeight
    fiberMultiplicity := fiberMultiplicity
    Dm := Dm
    tvDistance := tvDistance
    denominatorBound := denominatorBound
    tvAsMissingMass := hTvAsMissingMass
    missingMassLeDenominator := hMissingMassLe
    denominatorLeDmSq := hDenominatorLe
  }
  have hTvBound : tvDistance ≤ (Dm : ℝ) ^ (2 : ℕ) :=
    paper_pom_escort_maxfiber_tv_bound hEscort
  let hFrozen : Omega.Conclusion.FrozenEscortTvRigidityData := {
    α := α
    instFintype := inferInstance
    instDecEq := inferInstance
    maxFiber := maxFiber
    escortLaw := escortLaw
    uniformLaw := uniformLaw
    tvDistance := tvDistance
    massOnMaxFiber := massOnMaxFiber
    exponentialGap := exponentialGap
    tvDistance_def := hTvDef
    uniform_off_max := hUniformOff
    escort_eq_uniform_on_max := hEscortEq
    escort_nonneg := hEscortNonneg
    escort_total_mass := hEscortTotal
    massOnMaxFiber_def := hMassOnMax
    missingMass_exp_bound := hGapBound
  }
  have hFrozenPkg := Omega.Conclusion.paper_conclusion_frozen_escort_tv_rigidity hFrozen
  rcases hFrozenPkg with ⟨hTvExact, hTvExp⟩
  refine ⟨hTvExact, hTvExp, hTvBound, hκ_nonneg, ?_, ?_⟩
  · calc
      logM - κ ≤ logM * ε := hκ_le
      _ = logM * (1 - massOnMaxFiber) := by rw [hε]
      _ = logM * tvDistance := by rw [← hTvExact]
  · calc
      H = pomBinaryEntropy ε + (1 - ε) * logN + remainder := hEntropyDecomp
      _ ≤ pomBinaryEntropy ε + (1 - ε) * logN + ε * logN := by linarith
      _ = pomBinaryEntropy ε + logN := by ring

end Omega.POM
