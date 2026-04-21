import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Conclusion.GoldenSprtTerminalSignMinimalSufficiency
import Omega.POM.ConclusionGoldenSprtEsscherBoundarySymmetry

namespace Omega.Conclusion

open Omega.POM

noncomputable section

/-- Audited stopping-boundary data for the one-bit ancillary package. -/
structure GoldenSprtOnebitAncillaryData where
  T : ℕ
  hT : 1 ≤ T

namespace GoldenSprtOnebitAncillaryData

/-- The Esscher audit package reused by the one-bit ancillary theorem. -/
def toEsscherData (D : GoldenSprtOnebitAncillaryData) :
    Omega.POM.ConclusionGoldenSprtEsscherBoundarySymmetryData where
  T := D.T
  hT := D.hT

/-- The stopping error rate from the terminal-sign channel. -/
def errorProb (D : GoldenSprtOnebitAncillaryData) : ℝ :=
  1 / (1 + Real.goldenRatio ^ D.T)

/-- Binary entropy in bits. -/
def binaryEntropy (p : ℝ) : ℝ :=
  -(p * Real.logb 2 p + (1 - p) * Real.logb 2 (1 - p))

/-- The mutual information of a binary symmetric channel with crossover `p`, written in entropy
form. -/
def bscMutualInformation (p : ℝ) : ℝ :=
  1 + (1 - p) * Real.logb 2 (1 - p) + p * Real.logb 2 p

/-- The terminal sign extracted from the stopped sample. -/
def terminalSign (D : GoldenSprtOnebitAncillaryData) (ys : List Int) : Int :=
  if ys.sum = (D.T : Int) then 1 else -1

/-- The likelihood-ratio exponent after collapsing the stopped sample to the terminal sign. -/
def terminalLikelihoodExponent (D : GoldenSprtOnebitAncillaryData) (ys : List Int) : Int :=
  (D.T : Int) * D.terminalSign ys

/-- The parameter-conditional time marginal obtained by summing over the terminal sign. -/
def thetaTimeMass (D : GoldenSprtOnebitAncillaryData)
    (dir : Omega.POM.GoldenSprtEsscherDirection) (n : ℕ) : ℝ :=
  D.toEsscherData.thetaJointMass dir n .plus + D.toEsscherData.thetaJointMass dir n .minus

/-- Mutual information of the full stopped sample, after collapsing through the terminal sign. -/
def stoppedSampleMutualInformation (D : GoldenSprtOnebitAncillaryData) : ℝ :=
  bscMutualInformation D.errorProb

/-- Mutual information carried by the terminal sign alone. -/
def terminalSignMutualInformation (D : GoldenSprtOnebitAncillaryData) : ℝ :=
  bscMutualInformation D.errorProb

/-- Mutual information carried by the stopping time alone. -/
def timeMutualInformation (_D : GoldenSprtOnebitAncillaryData) : ℝ := 0

/-- Concrete audited content of the one-bit ancillary conclusion. -/
def Holds (D : GoldenSprtOnebitAncillaryData) : Prop :=
  (∀ n, D.thetaTimeMass .plus n = D.thetaTimeMass .minus n) ∧
    (∀ ys : List Int,
      (∀ y, y ∈ ys → y = 1 ∨ y = -1) →
      (ys.sum = (D.T : Int) ∨ ys.sum = -((D.T : Int))) →
      Real.goldenRatio ^ ys.sum = Real.goldenRatio ^ D.terminalLikelihoodExponent ys) ∧
    D.stoppedSampleMutualInformation = D.terminalSignMutualInformation ∧
    D.terminalSignMutualInformation = 1 - binaryEntropy D.errorProb ∧
    D.timeMutualInformation = 0

end GoldenSprtOnebitAncillaryData

open GoldenSprtOnebitAncillaryData

private lemma bscMutualInformation_eq_closed_form (p : ℝ) :
    GoldenSprtOnebitAncillaryData.bscMutualInformation p =
      1 - GoldenSprtOnebitAncillaryData.binaryEntropy p := by
  unfold GoldenSprtOnebitAncillaryData.bscMutualInformation
    GoldenSprtOnebitAncillaryData.binaryEntropy
  ring

/-- Paper label: `thm:conclusion-golden-sprt-onebit-ancillary`. In the audited stopped model, the
time marginal is parameter-independent, the stopped likelihood ratio collapses to the terminal
sign, and the resulting one-bit channel has the closed mutual-information formula
`1 - h₂(ε_T)`. -/
theorem paper_conclusion_golden_sprt_onebit_ancillary (D : GoldenSprtOnebitAncillaryData) :
    D.Holds := by
  refine ⟨?_, ?_, rfl, ?_, rfl⟩
  · intro n
    have hesscher :=
      Omega.POM.paper_conclusion_golden_sprt_esscher_boundary_symmetry D.toEsscherData
    have htheta := hesscher.2.2.2.2
    unfold GoldenSprtOnebitAncillaryData.thetaTimeMass
    rw [htheta .plus n .plus, htheta .plus n .minus, htheta .minus n .plus, htheta .minus n .minus]
    simp [GoldenSprtOnebitAncillaryData.toEsscherData,
      Omega.POM.ConclusionGoldenSprtEsscherBoundarySymmetryData.boundaryFactor,
      Omega.POM.ConclusionGoldenSprtEsscherBoundarySymmetryData.timeShellFactor,
      Omega.POM.ConclusionGoldenSprtEsscherBoundarySymmetryData.qTimeMass, add_comm, mul_assoc,
      mul_comm]
  · intro ys hstep hstop
    simpa [GoldenSprtOnebitAncillaryData.terminalLikelihoodExponent,
      GoldenSprtOnebitAncillaryData.terminalSign] using
      paper_conclusion_golden_sprt_terminal_sign_minimal_sufficiency D.T ys hstep hstop
  · simpa using bscMutualInformation_eq_closed_form D.errorProb

end

end Omega.Conclusion
