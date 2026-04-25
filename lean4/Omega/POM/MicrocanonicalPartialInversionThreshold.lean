import Mathlib.Tactic
import Omega.POM.TypeclassHammingBallVolumeVariational
import Omega.POM.TypeclassRateDistortionMutualInformation

namespace Omega.POM

noncomputable section

/-- Concrete threshold data for partial inversion in a fixed typeclass. The Hamming-ball
variational package provides the exponent `V_w(δ)`, `entropy` encodes the ambient typeclass
cardinality exponent `H(w)`, and `rate` is the side-information rate `r`. The stored
`subcriticalSuccessExponent` is any success exponent obtained from the union bound. -/
structure pom_microcanonical_partial_inversion_threshold_data where
  pom_microcanonical_partial_inversion_threshold_variational :
    pom_typeclass_hamming_ball_volume_variational_data
  pom_microcanonical_partial_inversion_threshold_entropy : ℝ
  pom_microcanonical_partial_inversion_threshold_rate : ℝ
  pom_microcanonical_partial_inversion_threshold_subcriticalSuccessExponent : ℝ
  pom_microcanonical_partial_inversion_threshold_unionBound :
    pom_microcanonical_partial_inversion_threshold_subcriticalSuccessExponent ≤
      pom_microcanonical_partial_inversion_threshold_rate +
        pom_microcanonical_partial_inversion_threshold_variational.volumeExponent -
          pom_microcanonical_partial_inversion_threshold_entropy

namespace pom_microcanonical_partial_inversion_threshold_data

/-- The covering exponent `R_w(δ) = H(w) - V_w(δ)`. -/
def pom_microcanonical_partial_inversion_threshold_coveringExponent
    (D : pom_microcanonical_partial_inversion_threshold_data) : ℝ :=
  D.pom_microcanonical_partial_inversion_threshold_entropy -
    D.pom_microcanonical_partial_inversion_threshold_variational.volumeExponent

/-- Subcritical union-bound exponent `r - R_w(δ)`. -/
def pom_microcanonical_partial_inversion_threshold_subcriticalBound
    (D : pom_microcanonical_partial_inversion_threshold_data) : ℝ :=
  D.pom_microcanonical_partial_inversion_threshold_rate -
    D.pom_microcanonical_partial_inversion_threshold_coveringExponent

/-- Supercritical covering slack `r - R_w(δ)`. -/
def pom_microcanonical_partial_inversion_threshold_supercriticalSlack
    (D : pom_microcanonical_partial_inversion_threshold_data) : ℝ :=
  D.pom_microcanonical_partial_inversion_threshold_rate -
    D.pom_microcanonical_partial_inversion_threshold_coveringExponent

/-- Paper-facing threshold package. The variational principle fixes the Hamming-ball exponent,
the rate-distortion wrapper identifies the covering exponent, the union bound gives the
subcritical decay exponent, and the supercritical regime is detected by positive covering slack. -/
def statement (D : pom_microcanonical_partial_inversion_threshold_data) : Prop :=
  IsGreatest
      (pom_typeclass_hamming_ball_volume_variational_objective_set
        D.pom_microcanonical_partial_inversion_threshold_variational)
      D.pom_microcanonical_partial_inversion_threshold_variational.volumeExponent ∧
    (∀ Hcond,
      Hcond ≤ D.pom_microcanonical_partial_inversion_threshold_variational.volumeExponent →
        D.pom_microcanonical_partial_inversion_threshold_coveringExponent ≤
          pomTypeclassMutualInformation
            D.pom_microcanonical_partial_inversion_threshold_entropy Hcond) ∧
    D.pom_microcanonical_partial_inversion_threshold_coveringExponent =
      pomTypeclassRateDistortionValue
        D.pom_microcanonical_partial_inversion_threshold_entropy
        D.pom_microcanonical_partial_inversion_threshold_variational.volumeExponent ∧
    D.pom_microcanonical_partial_inversion_threshold_subcriticalSuccessExponent ≤
      D.pom_microcanonical_partial_inversion_threshold_subcriticalBound ∧
    (D.pom_microcanonical_partial_inversion_threshold_rate <
        D.pom_microcanonical_partial_inversion_threshold_coveringExponent →
      D.pom_microcanonical_partial_inversion_threshold_subcriticalSuccessExponent < 0) ∧
    (D.pom_microcanonical_partial_inversion_threshold_coveringExponent <
        D.pom_microcanonical_partial_inversion_threshold_rate →
      0 < D.pom_microcanonical_partial_inversion_threshold_supercriticalSlack)

end pom_microcanonical_partial_inversion_threshold_data

open pom_microcanonical_partial_inversion_threshold_data

/-- Paper label: `thm:pom-microcanonical-partial-inversion-threshold`. The Hamming-ball
variational theorem provides the volume exponent `V_w(δ)`, the rate-distortion wrapper identifies
the covering exponent `R_w(δ) = H(w) - V_w(δ)`, the union bound yields the subcritical exponent
`r - R_w(δ)`, and the supercritical regime is exactly the positive-slack region
`r > R_w(δ)`. -/
theorem paper_pom_microcanonical_partial_inversion_threshold
    (D : pom_microcanonical_partial_inversion_threshold_data) : D.statement := by
  let hVariational :=
    paper_pom_typeclass_hamming_ball_volume_variational
      D.pom_microcanonical_partial_inversion_threshold_variational
  let hRateDistortion :=
    paper_pom_typeclass_rate_distortion_mutual_information
      D.pom_microcanonical_partial_inversion_threshold_entropy
      D.pom_microcanonical_partial_inversion_threshold_variational.volumeExponent
  rcases hRateDistortion with ⟨hOptimality, hExact, _⟩
  have hSubcriticalBound :
      D.pom_microcanonical_partial_inversion_threshold_subcriticalSuccessExponent ≤
        D.pom_microcanonical_partial_inversion_threshold_subcriticalBound := by
    dsimp [pom_microcanonical_partial_inversion_threshold_subcriticalBound,
      pom_microcanonical_partial_inversion_threshold_coveringExponent]
    linarith [D.pom_microcanonical_partial_inversion_threshold_unionBound]
  refine ⟨hVariational.1, ?_, ?_, hSubcriticalBound, ?_, ?_⟩
  · intro Hcond hcond
    have hopt := hOptimality Hcond hcond
    simpa [pom_microcanonical_partial_inversion_threshold_coveringExponent,
      pomTypeclassRateDistortionValue] using hopt
  · rfl
  · intro hSubcritical
    have hSubcritical' := hSubcritical
    dsimp [pom_microcanonical_partial_inversion_threshold_coveringExponent] at hSubcritical'
    have hBoundNeg :
        D.pom_microcanonical_partial_inversion_threshold_subcriticalBound < 0 := by
      dsimp [pom_microcanonical_partial_inversion_threshold_subcriticalBound,
        pom_microcanonical_partial_inversion_threshold_coveringExponent]
      linarith
    exact lt_of_le_of_lt hSubcriticalBound hBoundNeg
  · intro hSupercritical
    have hSupercritical' := hSupercritical
    dsimp [pom_microcanonical_partial_inversion_threshold_coveringExponent] at hSupercritical'
    dsimp [pom_microcanonical_partial_inversion_threshold_supercriticalSlack,
      pom_microcanonical_partial_inversion_threshold_coveringExponent]
    linarith

end
end Omega.POM
