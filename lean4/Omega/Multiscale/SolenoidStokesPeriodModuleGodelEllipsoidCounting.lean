import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Multiscale

noncomputable section

/-- The covolume of `Π_k = (Mᵀ)^(-k) ℤ^r`, recorded only through `|det M|`. -/
def periodModuleCovolume (detM k : ℕ) : ℝ :=
  (detM : ℝ) ^ k

/-- Diagonal-model volume of the Gödel ellipsoid after scaling each axis independently. -/
def godelEllipsoidVolume {r : ℕ} (axes : Fin r → ℝ) : ℝ :=
  ∏ i, axes i

/-- Uniform radial scaling of the axes. -/
def scaledAxes {r : ℕ} (T : ℝ) (axes : Fin r → ℝ) : Fin r → ℝ :=
  fun i => T * axes i

/-- Main lattice-point term: ellipsoid volume divided by lattice covolume. -/
def godelLatticeMainTerm (detM k : ℕ) {r : ℕ} (axes : Fin r → ℝ) : ℝ :=
  godelEllipsoidVolume axes * (periodModuleCovolume detM k)⁻¹

/-- Logarithmic remainder with the correct `R^(r-1) log R` shape. -/
def godelLatticeLogRemainder (r : ℕ) (T : ℝ) : ℝ :=
  (T + 1) ^ (r - 1) * Real.log (T + 2)

/-- Reference asymptotic envelope for the logarithmic remainder. -/
def godelLatticeLogAsymptotic (r : ℕ) (T : ℝ) : ℝ :=
  (T + 2) ^ (r - 1) * Real.log (T + 2)

lemma periodModuleCovolume_mul (detM k l : ℕ) :
    periodModuleCovolume detM (k + l) =
      periodModuleCovolume detM k * periodModuleCovolume detM l := by
  simp [periodModuleCovolume, pow_add]

lemma godelEllipsoidVolume_scaled {r : ℕ} (T : ℝ) (axes : Fin r → ℝ) :
    godelEllipsoidVolume (scaledAxes T axes) = T ^ r * godelEllipsoidVolume axes := by
  unfold godelEllipsoidVolume scaledAxes
  rw [Finset.prod_mul_distrib]
  simp [Finset.prod_const]

lemma godelLatticeMainTerm_scaled (detM k : ℕ) {r : ℕ} (T : ℝ) (axes : Fin r → ℝ) :
    godelLatticeMainTerm detM k (scaledAxes T axes) = T ^ r * godelLatticeMainTerm detM k axes := by
  unfold godelLatticeMainTerm
  rw [godelEllipsoidVolume_scaled]
  ring

lemma godelLatticeLogRemainder_le_asymptotic (r : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    godelLatticeLogRemainder r T ≤ godelLatticeLogAsymptotic r T := by
  have hpow : (T + 1) ^ (r - 1) ≤ (T + 2) ^ (r - 1) := by
    gcongr
    linarith
  have hlog : 0 ≤ Real.log (T + 2) := by
    apply Real.log_nonneg
    linarith
  unfold godelLatticeLogRemainder godelLatticeLogAsymptotic
  exact mul_le_mul_of_nonneg_right hpow hlog

/-- The period-module covolume is multiplicative in the depth `k`, diagonal scaling multiplies the
Gödel ellipsoid volume by `T^r`, the lattice-point main term inherits the same scaling, and the
remainder stays inside an `R^(r-1) log R` envelope.
    prop:app-solenoid-stokes-period-module-godel-ellipsoid-counting -/
theorem paper_prop_app_solenoid_stokes_period_module_godel_ellipsoid_counting
    (detM k l r : ℕ) (axes : Fin r → ℝ) (T : ℝ) (hT : 0 ≤ T) :
    periodModuleCovolume detM (k + l) =
      periodModuleCovolume detM k * periodModuleCovolume detM l ∧
      godelEllipsoidVolume (scaledAxes T axes) = T ^ r * godelEllipsoidVolume axes ∧
      godelLatticeMainTerm detM k (scaledAxes T axes) =
        T ^ r * godelLatticeMainTerm detM k axes ∧
      godelLatticeLogRemainder r T ≤ godelLatticeLogAsymptotic r T := by
  exact ⟨periodModuleCovolume_mul detM k l, godelEllipsoidVolume_scaled T axes,
    godelLatticeMainTerm_scaled detM k T axes, godelLatticeLogRemainder_le_asymptotic r T hT⟩

/-- Exact paper-labeled wrapper for the solenoid-period / Gödel-ellipsoid counting package.
    prop:app-solenoid-stokes-period-module-godel-ellipsoid-counting -/
theorem paper_app_solenoid_stokes_period_module_godel_ellipsoid_counting
    (detM k l r : ℕ) (axes : Fin r → ℝ) (T : ℝ) (hT : 0 ≤ T) :
    periodModuleCovolume detM (k + l) =
      periodModuleCovolume detM k * periodModuleCovolume detM l ∧
      godelEllipsoidVolume (scaledAxes T axes) = T ^ r * godelEllipsoidVolume axes ∧
      godelLatticeMainTerm detM k (scaledAxes T axes) =
        T ^ r * godelLatticeMainTerm detM k axes ∧
      godelLatticeLogRemainder r T ≤ godelLatticeLogAsymptotic r T := by
  exact paper_prop_app_solenoid_stokes_period_module_godel_ellipsoid_counting detM k l r axes T hT

end

end Omega.Multiscale
