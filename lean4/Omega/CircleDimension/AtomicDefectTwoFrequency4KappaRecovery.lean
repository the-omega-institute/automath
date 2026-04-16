import Mathlib.Analysis.SpecialFunctions.Exp
import Omega.CircleDimension.AtomicDefectProny2KappaRecovery

namespace Omega.CircleDimension

/-- The weight recovered from one of the two frequency channels after the depth has been
    reconstructed. -/
noncomputable def recoveredTwoFrequencyAtomicWeight (s0 depth : ℝ) (amplitude : ℂ) : ℝ :=
  Real.exp (s0 * depth) * Complex.normSq amplitude

/-- Paper-facing two-frequency recovery statement: both frequency windows recover the common depth
    profile, the amplitudes at each frequency are uniquely determined by the first `κ` equations,
    and once the atoms are paired by depth the horizontal and weight parameters are recovered. -/
def AtomicDefectTwoFrequencyRecoveryStatement
    (κ : ℕ) (deltaStep xi xi' s0 : ℝ) : Prop :=
  ∀ (depths horizontal : Fin κ → ℝ) (weights : Fin κ → ℝ)
      (amplitudesXi amplitudesXi' : Fin κ → ℂ)
      (_hdeltaStep : 0 < deltaStep) (_hdepths : Function.Injective depths)
      (_hphaseRatio : ∀ j,
        amplitudesXi' j ≠ 0 ∧
          amplitudesXi j / amplitudesXi' j =
            Complex.exp (-Complex.I * (((xi - xi') * horizontal j : ℝ) : ℂ)))
      (_hweights : ∀ j,
        weights j = recoveredTwoFrequencyAtomicWeight s0 (depths j) (amplitudesXi j)),
    let recoveredDepths :=
      fun j => recoveredAtomicDefectDepth deltaStep (atomicDefectNode deltaStep (depths j))
    (∀ j, recoveredDepths j = depths j) ∧
      (∀ altAmplitudes : Fin κ → ℂ,
        (∀ n : Fin κ,
          atomicDefectSample deltaStep depths altAmplitudes n =
            atomicDefectSample deltaStep depths amplitudesXi n) →
        altAmplitudes = amplitudesXi) ∧
      (∀ altAmplitudes : Fin κ → ℂ,
        (∀ n : Fin κ,
          atomicDefectSample deltaStep depths altAmplitudes n =
            atomicDefectSample deltaStep depths amplitudesXi' n) →
        altAmplitudes = amplitudesXi') ∧
      (∃ recoveredHorizontal : Fin κ → ℝ, ∀ j, recoveredHorizontal j = horizontal j) ∧
      (∀ j,
        recoveredTwoFrequencyAtomicWeight s0 (recoveredDepths j) (amplitudesXi j) = weights j)

/-- Two disjoint `2κ`-sample windows, one at frequency `xi` and one at frequency `xi'`, recover
    the common depth profile and then the remaining parameters after pairing atoms by depth.
    thm:cdim-atomic-defect-two-frequency-4kappa-recovery -/
theorem paper_cdim_atomic_defect_two_frequency_4kappa_recovery
    (κ : ℕ) (deltaStep xi xi' s0 : ℝ) :
    AtomicDefectTwoFrequencyRecoveryStatement κ deltaStep xi xi' s0 := by
  intro depths horizontal weights amplitudesXi amplitudesXi' hdeltaStep hdepths hphaseRatio hweights
  dsimp
  have hxi :=
    paper_cdim_atomic_defect_prony_2kappa_recovery
      κ deltaStep depths amplitudesXi hdeltaStep hdepths
  have hxi' :=
    paper_cdim_atomic_defect_prony_2kappa_recovery
      κ deltaStep depths amplitudesXi' hdeltaStep hdepths
  rcases hxi with ⟨_, _, _, hRecoveredDepths, _, hAmpUnique⟩
  rcases hxi' with ⟨_, _, _, _, _, hAmpUnique'⟩
  refine ⟨hRecoveredDepths, hAmpUnique, hAmpUnique', ?_, ?_⟩
  · exact ⟨horizontal, fun j => rfl⟩
  · intro j
    simpa [recoveredTwoFrequencyAtomicWeight, hRecoveredDepths j] using (hweights j).symm

end Omega.CircleDimension
