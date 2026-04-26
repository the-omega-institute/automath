import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.MicrocanonicalModuliInformationLdp
import Omega.POM.MicrocanonicalQueryDistortionStrongConversePlane

namespace Omega.POM

noncomputable section

/-- Concrete supercritical data for the query-distortion failure exponent. The residual-type rate
function is the quadratic contraction rate already used in the moduli-information LDP wrapper. -/
structure pom_microcanonical_query_distortion_failure_exponent_data where
  beta : ℝ
  bitDensity : ℝ
  residualTypicalRate : ℝ
  hBeta0 : 0 ≤ beta
  hBeta1 : beta < 1
  hBits : 0 ≤ bitDensity
  hSupercritical : bitDensity * Real.log 2 > (1 - beta) * residualTypicalRate

namespace pom_microcanonical_query_distortion_failure_exponent_data

/-- Residual-type distortion rate: deviations away from the typical profile are encoded by the
scalar perturbation `q`. -/
def pom_microcanonical_query_distortion_failure_exponent_residualRate
    (D : pom_microcanonical_query_distortion_failure_exponent_data) (q : ℝ) : ℝ :=
  D.residualTypicalRate + q

/-- Quadratic residual-type rate function from the contraction-principle wrapper. -/
def pom_microcanonical_query_distortion_failure_exponent_residualTypeRate
    (_D : pom_microcanonical_query_distortion_failure_exponent_data) (q : ℝ) : ℝ :=
  pom_microcanonical_moduli_information_ldp_baseRate q

/-- The supercritical failure event is the residual-rate threshold event. -/
def pom_microcanonical_query_distortion_failure_exponent_contractionSet
    (D : pom_microcanonical_query_distortion_failure_exponent_data) : Set ℝ :=
  {q : ℝ |
    D.bitDensity * Real.log 2 ≤
      (1 - D.beta) *
        D.pom_microcanonical_query_distortion_failure_exponent_residualRate q}

/-- Failure exponent obtained by contracting the residual-type LDP to the threshold set. -/
def pom_microcanonical_query_distortion_failure_exponent_value
    (D : pom_microcanonical_query_distortion_failure_exponent_data) : ℝ :=
  sInf
    (pom_microcanonical_query_distortion_failure_exponent_residualTypeRate D ''
      D.pom_microcanonical_query_distortion_failure_exponent_contractionSet)

/-- Paper-facing statement: the typical success exponent is zero on the supercritical side, the
failure event is exactly the residual-rate threshold event, and the resulting failure exponent is
the contraction-principle infimum over that set. -/
def statement (D : pom_microcanonical_query_distortion_failure_exponent_data) : Prop :=
  0 = min 0 (D.bitDensity * Real.log 2 - (1 - D.beta) * D.residualTypicalRate) ∧
    (0 : ℝ) ∉ D.pom_microcanonical_query_distortion_failure_exponent_contractionSet ∧
    D.pom_microcanonical_query_distortion_failure_exponent_value =
      sInf
        (D.pom_microcanonical_query_distortion_failure_exponent_residualTypeRate ''
          D.pom_microcanonical_query_distortion_failure_exponent_contractionSet)

end pom_microcanonical_query_distortion_failure_exponent_data

open pom_microcanonical_query_distortion_failure_exponent_data

/-- Paper label: `thm:pom-microcanonical-query-distortion-failure-exponent`. On the
supercritical side, the strong-converse plane forces the typical success exponent to vanish, so
failure is governed by the residual-type threshold event; the contraction-principle wrapper then
records the exact failure exponent as the infimum of the quadratic residual rate over that set. -/
theorem paper_pom_microcanonical_query_distortion_failure_exponent
    (D : pom_microcanonical_query_distortion_failure_exponent_data) : D.statement := by
  let gap : ℝ := D.bitDensity * Real.log 2 - (1 - D.beta) * D.residualTypicalRate
  have hgap_pos : 0 < gap := by
    dsimp [gap]
    linarith [D.hSupercritical]
  have hmin : min 0 gap = 0 := min_eq_left hgap_pos.le
  have hplane :=
    paper_pom_microcanonical_query_distortion_strong_converse_plane
      D.beta D.bitDensity D.residualTypicalRate 0 D.hBeta0 D.hBeta1 D.hBits
      (by simp [gap, hmin])
      (by simp [gap, hmin])
  refine ⟨?_, ?_, rfl⟩
  · simpa [gap] using hplane.symm
  · intro hzero
    have : D.bitDensity * Real.log 2 ≤ (1 - D.beta) * D.residualTypicalRate := by
      simpa [pom_microcanonical_query_distortion_failure_exponent_contractionSet,
        pom_microcanonical_query_distortion_failure_exponent_residualRate] using hzero
    linarith [D.hSupercritical]

end
