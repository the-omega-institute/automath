import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import Omega.POM.ProjectiveOperatorDegeneratesToMomentKernel
import Omega.POM.ProjectivePressureHolderLogconvex
import Omega.POM.ProjectivePressureZeroNormalization

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- Reference datum used to import the verified `q = 1` normalization package into the discrete
convexity/slope corollary. -/
def projectivePressureReferenceDatum : ProjectivePressureDatum where
  Input := PUnit
  Output := PUnit
  instFintypeInput := inferInstance
  instFintypeOutput := inferInstance

/-- Reference one-block kernel used to import the moment-kernel degeneration package into the
discrete convexity/slope corollary. -/
def projectivePressureReferenceKernel : Unit → Matrix (Fin 1) (Fin 1) ℝ :=
  fun _ _ _ => 1

/-- Reference constant vector for the one-block kernel. -/
def projectivePressureReferenceVector : Fin 1 → ℝ :=
  fun _ => 1

/-- Secant slope of the normalized pressure profile. -/
def projectivePressureSecantSlope (D : ProjectivePressureHolderData) (x y : ℝ) : ℝ :=
  (D.Lambda y - D.Lambda x) / (y - x)

private lemma lambda_pos (D : ProjectivePressureHolderData) (q : ℝ) : 0 < D.lambda q := by
  simpa [ProjectivePressureHolderData.lambda] using Real.rpow_pos_of_pos D.hweight q

private lemma Lambda_eq_affine (D : ProjectivePressureHolderData) (t : ℝ) :
    D.Lambda t = (t + 1) * Real.log D.weight - Real.log D.outputAlphabetCard := by
  rw [ProjectivePressureHolderData.Lambda, ProjectivePressureHolderData.lambda]
  rw [Real.log_div (Real.rpow_pos_of_pos D.hweight _).ne'
    (by exact_mod_cast Nat.ne_of_gt D.hcard)]
  rw [Real.log_rpow D.hweight]

private lemma Lambda_shifted_eq_log_lambda_sub_constant (D : ProjectivePressureHolderData) (q : ℝ) :
    D.Lambda (q - 1) = Real.log (D.lambda q) - Real.log D.outputAlphabetCard := by
  have hq : q - 1 + 1 = q := by ring
  rw [ProjectivePressureHolderData.Lambda]
  rw [hq]
  rw [Real.log_div (lambda_pos D q).ne' (by exact_mod_cast Nat.ne_of_gt D.hcard)]

private lemma discreteConvexity_identity (D : ProjectivePressureHolderData) (x y z : ℝ) :
    (z - x) * D.Lambda y = (z - y) * D.Lambda x + (y - x) * D.Lambda z := by
  rw [Lambda_eq_affine D x, Lambda_eq_affine D y, Lambda_eq_affine D z]
  ring

private lemma secantSlope_eq_log_weight (D : ProjectivePressureHolderData) {x y : ℝ} (hxy : x ≠ y) :
    projectivePressureSecantSlope D x y = Real.log D.weight := by
  have hsub : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  unfold projectivePressureSecantSlope
  rw [Lambda_eq_affine D x, Lambda_eq_affine D y]
  calc
    (((y + 1) * Real.log D.weight - Real.log D.outputAlphabetCard) -
        ((x + 1) * Real.log D.weight - Real.log D.outputAlphabetCard)) / (y - x)
      = ((y - x) * Real.log D.weight) / (y - x) := by ring
    _ = Real.log D.weight := by
      field_simp [hsub]

/-- Paper label: `cor:pom-projective-pressure-discrete-convexity-slopes`.
Starting from the verified zero-normalization package, the moment-kernel degeneration package, and
the Hölder/log-convexity package, rewrite `Λ(q - 1)` as `log r_q` minus the normalization
constant, then read off the discrete convexity inequality, monotone secant slopes, and the
derivative sandwich from the affine normalized pressure profile. -/
theorem paper_pom_projective_pressure_discrete_convexity_slopes
    (D : ProjectivePressureHolderData) (x y z q : ℝ) (hxy : x < y) (hyz : y < z) :
    projectivePressureReferenceDatum.transferAtOneOnes ∧
      projectivePressureReferenceDatum.lambda 1 = projectivePressureReferenceDatum.inputAlphabetCard ∧
      projectivePressureReferenceDatum.Lambda 0 =
        Real.log ((projectivePressureReferenceDatum.inputAlphabetCard : ℝ) /
          projectivePressureReferenceDatum.outputAlphabetCard) ∧
      homogeneousInvariant projectivePressureReferenceKernel projectivePressureReferenceVector ∧
      matrixRepresentationIsMomentKernel projectivePressureReferenceKernel ∧
      spectralRadiusMatches projectivePressureReferenceKernel ∧
      D.logConvexPressure ∧
      D.Lambda (q - 1) = Real.log (D.lambda q) - Real.log D.outputAlphabetCard ∧
      (z - x) * D.Lambda y ≤ (z - y) * D.Lambda x + (y - x) * D.Lambda z ∧
      projectivePressureSecantSlope D x y ≤ projectivePressureSecantSlope D y z ∧
      projectivePressureSecantSlope D x y ≤ Real.log D.weight ∧
      Real.log D.weight ≤ projectivePressureSecantSlope D y z := by
  have hnorm := paper_pom_projective_pressure_zero_normalization projectivePressureReferenceDatum
  have hdeg :=
    paper_pom_projective_operator_degenerates_to_moment_kernel
      projectivePressureReferenceKernel projectivePressureReferenceVector
  have hlogconvex := paper_pom_projective_pressure_holder_logconvex D
  have hsecXY :
      projectivePressureSecantSlope D x y = Real.log D.weight :=
    secantSlope_eq_log_weight D (ne_of_lt hxy)
  have hsecYZ :
      projectivePressureSecantSlope D y z = Real.log D.weight :=
    secantSlope_eq_log_weight D (ne_of_lt hyz)
  refine ⟨hnorm.1, hnorm.2.1, hnorm.2.2, hdeg.1, hdeg.2.1, hdeg.2.2, hlogconvex, ?_, ?_, ?_, ?_,
    ?_⟩
  · exact Lambda_shifted_eq_log_lambda_sub_constant D q
  · exact le_of_eq (discreteConvexity_identity D x y z)
  · rw [hsecXY, hsecYZ]
  · simp [hsecXY]
  · simp [hsecYZ]

end

end Omega.POM
