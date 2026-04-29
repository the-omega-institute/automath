import Mathlib.Tactic
import Omega.Folding.CollisionKernel
import Omega.SyncKernelWeighted.WeightedNewmanThreshold

namespace Omega.POM

open Omega.SyncKernelWeighted

/-- Audited `E₆` threshold from the A₄/ADE comparison table. -/
def pom_a4t_newman_threshold_ade_ordering_tE6 : ℚ := 31 / 5

/-- Audited Newman threshold. -/
def pom_a4t_newman_threshold_ade_ordering_tStar : ℚ := 13 / 2

/-- Audited `E₇` threshold from the A₄/ADE comparison table. -/
def pom_a4t_newman_threshold_ade_ordering_tE7 : ℚ := 29 / 4

/-- Audited `E₈` threshold from the A₄/ADE comparison table. -/
def pom_a4t_newman_threshold_ade_ordering_tE8 : ℚ := 15 / 2

/-- The concrete weighted Newman certificate used for the threshold comparison. -/
def pom_a4t_newman_threshold_ade_ordering_certificate : WeightedNewmanThresholdData where
  uStar := 1
  threshold := pom_a4t_newman_threshold_ade_ordering_tStar
  residualSlope := 1
  residualIntercept := 1

/-- Package for the strict ADE/Newman ordering around `t = 7`. -/
def pom_a4t_newman_threshold_ade_ordering_package : Prop :=
  Omega.a4CharPoly 7 0 = 2 ∧
    Omega.a4CharPoly 7 1 = -8 ∧
    pom_a4t_newman_threshold_ade_ordering_certificate.resultantFactorization ∧
    pom_a4t_newman_threshold_ade_ordering_certificate.uniqueCriticalRoot ∧
    pom_a4t_newman_threshold_ade_ordering_certificate.rhStrictBelowThreshold ∧
    pom_a4t_newman_threshold_ade_ordering_certificate.rhSharpAtThreshold ∧
    pom_a4t_newman_threshold_ade_ordering_certificate.rhFailsAboveThreshold ∧
    pom_a4t_newman_threshold_ade_ordering_certificate.threshold =
      pom_a4t_newman_threshold_ade_ordering_tStar ∧
    pom_a4t_newman_threshold_ade_ordering_tE6 < pom_a4t_newman_threshold_ade_ordering_tStar ∧
    pom_a4t_newman_threshold_ade_ordering_tStar < 7 ∧
    (7 : ℚ) < pom_a4t_newman_threshold_ade_ordering_tE7 ∧
    pom_a4t_newman_threshold_ade_ordering_tE7 < pom_a4t_newman_threshold_ade_ordering_tE8 ∧
    weightedNewmanSpectralGap pom_a4t_newman_threshold_ade_ordering_certificate 7 < 0

/-- Paper label: `cor:pom-a4t-newman-threshold-ade-ordering`. The audited `A₄/ADE` intersection
data at `t = 7` and the weighted Newman threshold certificate place the four constants in the
strict order `t_E6 < t_star < 7 < t_E7 < t_E8`. -/
theorem paper_pom_a4t_newman_threshold_ade_ordering : pom_a4t_newman_threshold_ade_ordering_package := by
  have hA4 := Omega.paper_pom_a4t_jones_ade_intersections
  have hWeighted := paper_sync_kernel_weighted_newman_threshold
    pom_a4t_newman_threshold_ade_ordering_certificate
  refine ⟨hA4.2.2.2.1, hA4.2.2.2.2, hWeighted.1, hWeighted.2.1, hWeighted.2.2.1, hWeighted.2.2.2.1,
    hWeighted.2.2.2.2, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [pom_a4t_newman_threshold_ade_ordering_tE6,
      pom_a4t_newman_threshold_ade_ordering_tStar]
  · norm_num [pom_a4t_newman_threshold_ade_ordering_tStar]
  · norm_num [pom_a4t_newman_threshold_ade_ordering_tE7]
  · norm_num [pom_a4t_newman_threshold_ade_ordering_tE7,
      pom_a4t_newman_threshold_ade_ordering_tE8]
  · norm_num [weightedNewmanSpectralGap, pom_a4t_newman_threshold_ade_ordering_certificate,
      pom_a4t_newman_threshold_ade_ordering_tStar]

end Omega.POM
