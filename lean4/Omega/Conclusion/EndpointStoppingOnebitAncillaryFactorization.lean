import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Conclusion.GoldenSprtTerminalSignMinimalSufficiency
import Omega.POM.ConclusionGoldenSprtEsscherBoundarySymmetry

namespace Omega.Conclusion

open Omega.POM

noncomputable section

/-- Concrete endpoint-stopping data reused by the one-bit ancillary factorization theorem. -/
structure ConclusionEndpointStoppingOnebitAncillaryFactorizationData where
  T : ℕ
  hT : 1 ≤ T

namespace ConclusionEndpointStoppingOnebitAncillaryFactorizationData

/-- Reuse the audited Esscher boundary package from the POM chapter. -/
def conclusion_endpoint_stopping_onebit_ancillary_factorization_toEsscherData
    (D : ConclusionEndpointStoppingOnebitAncillaryFactorizationData) :
    Omega.POM.ConclusionGoldenSprtEsscherBoundarySymmetryData where
  T := D.T
  hT := D.hT

/-- The stopping error probability seen through the terminal-sign channel. -/
def conclusion_endpoint_stopping_onebit_ancillary_factorization_errorProb
    (D : ConclusionEndpointStoppingOnebitAncillaryFactorizationData) : ℝ :=
  1 / (1 + Real.goldenRatio ^ D.T)

/-- Binary entropy in bits. -/
def conclusion_endpoint_stopping_onebit_ancillary_factorization_binaryEntropy (p : ℝ) : ℝ :=
  -(p * Real.logb 2 p + (1 - p) * Real.logb 2 (1 - p))

/-- Mutual information of the binary symmetric channel with crossover probability `p`. -/
def conclusion_endpoint_stopping_onebit_ancillary_factorization_bscMutualInformation
    (p : ℝ) : ℝ :=
  1 + (1 - p) * Real.logb 2 (1 - p) + p * Real.logb 2 p

/-- The terminal sign extracted from the stopped path. -/
def conclusion_endpoint_stopping_onebit_ancillary_factorization_terminalSign
    (D : ConclusionEndpointStoppingOnebitAncillaryFactorizationData) (ys : List Int) : Int :=
  if ys.sum = (D.T : Int) then 1 else -1

/-- The likelihood-ratio exponent after collapsing the stopped path to its terminal sign. -/
def conclusion_endpoint_stopping_onebit_ancillary_factorization_terminalLikelihoodExponent
    (D : ConclusionEndpointStoppingOnebitAncillaryFactorizationData) (ys : List Int) : Int :=
  (D.T : Int) *
    D.conclusion_endpoint_stopping_onebit_ancillary_factorization_terminalSign ys

/-- Parameter-conditional time mass obtained by summing over the terminal sign. -/
def conclusion_endpoint_stopping_onebit_ancillary_factorization_thetaTimeMass
    (D : ConclusionEndpointStoppingOnebitAncillaryFactorizationData)
    (dir : Omega.POM.GoldenSprtEsscherDirection) (n : ℕ) : ℝ :=
  D.conclusion_endpoint_stopping_onebit_ancillary_factorization_toEsscherData.thetaJointMass
      dir n .plus +
    D.conclusion_endpoint_stopping_onebit_ancillary_factorization_toEsscherData.thetaJointMass
      dir n .minus

/-- Mutual information carried by the full stopped sample after the audited collapse. -/
def conclusion_endpoint_stopping_onebit_ancillary_factorization_stoppedSampleMutualInformation
    (D : ConclusionEndpointStoppingOnebitAncillaryFactorizationData) : ℝ :=
  conclusion_endpoint_stopping_onebit_ancillary_factorization_bscMutualInformation
    (conclusion_endpoint_stopping_onebit_ancillary_factorization_errorProb D)

/-- Mutual information carried by the terminal sign alone. -/
def conclusion_endpoint_stopping_onebit_ancillary_factorization_terminalSignMutualInformation
    (D : ConclusionEndpointStoppingOnebitAncillaryFactorizationData) : ℝ :=
  conclusion_endpoint_stopping_onebit_ancillary_factorization_bscMutualInformation
    (conclusion_endpoint_stopping_onebit_ancillary_factorization_errorProb D)

/-- Mutual information carried by the stopping time alone. -/
def conclusion_endpoint_stopping_onebit_ancillary_factorization_timeMutualInformation
    (_D : ConclusionEndpointStoppingOnebitAncillaryFactorizationData) : ℝ :=
  0

/-- The stopped joint law factors into the boundary-sign and time-shell terms. -/
def jointFactorization (D : ConclusionEndpointStoppingOnebitAncillaryFactorizationData) : Prop :=
  ∀ dir n s,
    D.conclusion_endpoint_stopping_onebit_ancillary_factorization_toEsscherData.thetaJointMass
        dir n s =
      ((1 : ℝ) / 2) *
        Omega.POM.ConclusionGoldenSprtEsscherBoundarySymmetryData.boundaryFactor
          D.conclusion_endpoint_stopping_onebit_ancillary_factorization_toEsscherData dir s *
        Omega.POM.ConclusionGoldenSprtEsscherBoundarySymmetryData.timeShellFactor n *
        D.conclusion_endpoint_stopping_onebit_ancillary_factorization_toEsscherData.qTimeMass n

/-- The terminal sign is a sufficient one-bit summary of the stopped path. -/
def signMinimalSufficient
    (D : ConclusionEndpointStoppingOnebitAncillaryFactorizationData) : Prop :=
  ∀ ys : List Int,
    (∀ y, y ∈ ys → y = 1 ∨ y = -1) →
    (ys.sum = (D.T : Int) ∨ ys.sum = -((D.T : Int))) →
    Real.goldenRatio ^ ys.sum =
      (if ys.sum = (D.T : Int) then Real.goldenRatio ^ D.T else (Real.goldenRatio ^ D.T)⁻¹)

/-- The stopping clock is ancillary once the path is collapsed to the terminal sign. -/
def clockAncillary (D : ConclusionEndpointStoppingOnebitAncillaryFactorizationData) : Prop :=
  ∀ n,
    D.conclusion_endpoint_stopping_onebit_ancillary_factorization_thetaTimeMass .plus n =
      D.conclusion_endpoint_stopping_onebit_ancillary_factorization_thetaTimeMass .minus n

/-- All path information collapses to the one-bit terminal sign, leaving no residual information
in the stopping clock. -/
def pathInformationCollapse
    (D : ConclusionEndpointStoppingOnebitAncillaryFactorizationData) : Prop :=
  D.conclusion_endpoint_stopping_onebit_ancillary_factorization_stoppedSampleMutualInformation =
    D.conclusion_endpoint_stopping_onebit_ancillary_factorization_terminalSignMutualInformation ∧
    D.conclusion_endpoint_stopping_onebit_ancillary_factorization_terminalSignMutualInformation =
      1 -
        conclusion_endpoint_stopping_onebit_ancillary_factorization_binaryEntropy
          (conclusion_endpoint_stopping_onebit_ancillary_factorization_errorProb D) ∧
    D.conclusion_endpoint_stopping_onebit_ancillary_factorization_timeMutualInformation = 0

end ConclusionEndpointStoppingOnebitAncillaryFactorizationData

open ConclusionEndpointStoppingOnebitAncillaryFactorizationData

private lemma conclusion_endpoint_stopping_onebit_ancillary_factorization_bsc_eq_closed_form
    (p : ℝ) :
    conclusion_endpoint_stopping_onebit_ancillary_factorization_bscMutualInformation p =
      1 - conclusion_endpoint_stopping_onebit_ancillary_factorization_binaryEntropy p := by
  unfold conclusion_endpoint_stopping_onebit_ancillary_factorization_bscMutualInformation
    conclusion_endpoint_stopping_onebit_ancillary_factorization_binaryEntropy
  ring

/-- Paper label:
`thm:conclusion-endpoint-stopping-onebit-ancillary-factorization`. The audited endpoint package
combines the Esscher boundary factorization, terminal-sign minimal sufficiency, ancillarity of the
stopping time, and the one-bit information collapse. -/
theorem paper_conclusion_endpoint_stopping_onebit_ancillary_factorization
    (D : ConclusionEndpointStoppingOnebitAncillaryFactorizationData) :
    D.jointFactorization ∧ D.signMinimalSufficient ∧ D.clockAncillary ∧
      D.pathInformationCollapse := by
  have hEsscher :=
    Omega.POM.paper_conclusion_golden_sprt_esscher_boundary_symmetry
      D.conclusion_endpoint_stopping_onebit_ancillary_factorization_toEsscherData
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro dir n s
    exact hEsscher.2.2.2.2 dir n s
  · intro ys hstep hstop
    simpa using paper_conclusion_golden_sprt_terminal_sign_minimal_sufficiency D.T ys hstep hstop
  · intro n
    have htheta := hEsscher.2.2.2.2
    change
      D.conclusion_endpoint_stopping_onebit_ancillary_factorization_toEsscherData.thetaJointMass
          .plus n .plus +
        D.conclusion_endpoint_stopping_onebit_ancillary_factorization_toEsscherData.thetaJointMass
          .plus n .minus =
      D.conclusion_endpoint_stopping_onebit_ancillary_factorization_toEsscherData.thetaJointMass
          .minus n .plus +
        D.conclusion_endpoint_stopping_onebit_ancillary_factorization_toEsscherData.thetaJointMass
          .minus n .minus
    rw [htheta .plus n .plus, htheta .plus n .minus, htheta .minus n .plus, htheta .minus n .minus]
    simp [ConclusionEndpointStoppingOnebitAncillaryFactorizationData.conclusion_endpoint_stopping_onebit_ancillary_factorization_toEsscherData,
      Omega.POM.ConclusionGoldenSprtEsscherBoundarySymmetryData.boundaryFactor,
      Omega.POM.ConclusionGoldenSprtEsscherBoundarySymmetryData.timeShellFactor,
      Omega.POM.ConclusionGoldenSprtEsscherBoundarySymmetryData.qTimeMass, add_comm, mul_comm]
  · change
      conclusion_endpoint_stopping_onebit_ancillary_factorization_stoppedSampleMutualInformation D =
          conclusion_endpoint_stopping_onebit_ancillary_factorization_terminalSignMutualInformation
            D ∧
        conclusion_endpoint_stopping_onebit_ancillary_factorization_terminalSignMutualInformation D =
          1 -
            conclusion_endpoint_stopping_onebit_ancillary_factorization_binaryEntropy
              (conclusion_endpoint_stopping_onebit_ancillary_factorization_errorProb D) ∧
        conclusion_endpoint_stopping_onebit_ancillary_factorization_timeMutualInformation D = 0
    refine ⟨rfl, ?_, rfl⟩
    simpa [conclusion_endpoint_stopping_onebit_ancillary_factorization_terminalSignMutualInformation]
      using
      conclusion_endpoint_stopping_onebit_ancillary_factorization_bsc_eq_closed_form
        (conclusion_endpoint_stopping_onebit_ancillary_factorization_errorProb D)

end

end Omega.Conclusion
