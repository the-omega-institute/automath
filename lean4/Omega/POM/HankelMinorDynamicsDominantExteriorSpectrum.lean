import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Concrete one-mode seed for the shifted Hankel/exterior-power comparison. The `1 × 1` model
captures the dominant exterior mode explicitly, so the distinguished Hankel minor is literally the
unique matrix entry and evolves by a first-order linear recurrence. -/
structure POMHankelMinorDynamicsDominantExteriorSpectrumData where
  dominantEigenvalue : ℝ
  spectralWeight : ℝ
  hdominant : 0 < dominantEigenvalue

/-- The shifted Hankel family carried by the dominant exterior mode. -/
def pom_hankel_minor_dynamics_dominant_exterior_spectrum_shiftedHankelFamily
    (D : POMHankelMinorDynamicsDominantExteriorSpectrumData) (r : ℕ) :
    Matrix (Fin 1) (Fin 1) ℝ :=
  fun _ _ => D.spectralWeight * D.dominantEigenvalue ^ r

/-- In the `1 × 1` model the exterior-power propagation family is the same matrix family. -/
def pom_hankel_minor_dynamics_dominant_exterior_spectrum_exteriorPowerFamily
    (D : POMHankelMinorDynamicsDominantExteriorSpectrumData) (r : ℕ) :
    Matrix (Fin 1) (Fin 1) ℝ :=
  pom_hankel_minor_dynamics_dominant_exterior_spectrum_shiftedHankelFamily D r

/-- The distinguished Hankel minor. -/
def pom_hankel_minor_dynamics_dominant_exterior_spectrum_minor
    (D : POMHankelMinorDynamicsDominantExteriorSpectrumData) (r : ℕ) : ℝ :=
  pom_hankel_minor_dynamics_dominant_exterior_spectrum_shiftedHankelFamily D r 0 0

/-- The same minor viewed as an exterior-power matrix entry. -/
def pom_hankel_minor_dynamics_dominant_exterior_spectrum_exteriorEntry
    (D : POMHankelMinorDynamicsDominantExteriorSpectrumData) (r : ℕ) : ℝ :=
  pom_hankel_minor_dynamics_dominant_exterior_spectrum_exteriorPowerFamily D r 0 0

/-- Paper-facing package: the distinguished minor is the exterior entry, the matrix family and the
minor inherit the one-step recurrence from the dominant exterior eigenvalue, and the normalized
minor sequence is constant. -/
def POMHankelMinorDynamicsDominantExteriorSpectrumData.package
    (D : POMHankelMinorDynamicsDominantExteriorSpectrumData) : Prop :=
  (∀ r,
      pom_hankel_minor_dynamics_dominant_exterior_spectrum_minor D r =
        pom_hankel_minor_dynamics_dominant_exterior_spectrum_exteriorEntry D r) ∧
    (∀ r,
      pom_hankel_minor_dynamics_dominant_exterior_spectrum_shiftedHankelFamily D (r + 1) =
        D.dominantEigenvalue •
          pom_hankel_minor_dynamics_dominant_exterior_spectrum_shiftedHankelFamily D r) ∧
    (∀ r,
      pom_hankel_minor_dynamics_dominant_exterior_spectrum_minor D (r + 1) =
        D.dominantEigenvalue * pom_hankel_minor_dynamics_dominant_exterior_spectrum_minor D r) ∧
    ∀ r,
      pom_hankel_minor_dynamics_dominant_exterior_spectrum_minor D r /
          D.dominantEigenvalue ^ r =
        D.spectralWeight

/-- Paper label: `thm:pom-hankel-minor-dynamics-dominant-exterior-spectrum`. In the concrete
single-dominant exterior mode, every shifted Hankel minor is the unique exterior entry, obeys the
propagated first-order recurrence, and after dividing by the dominant eigenvalue `λ^r` the minor
sequence stabilizes to the constant exterior spectral weight. -/
theorem paper_pom_hankel_minor_dynamics_dominant_exterior_spectrum
    (D : POMHankelMinorDynamicsDominantExteriorSpectrumData) : D.package := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r
    rfl
  · intro r
    ext i j
    simp [pom_hankel_minor_dynamics_dominant_exterior_spectrum_shiftedHankelFamily, pow_succ,
      mul_left_comm, mul_comm]
  · intro r
    simp [pom_hankel_minor_dynamics_dominant_exterior_spectrum_minor,
      pom_hankel_minor_dynamics_dominant_exterior_spectrum_shiftedHankelFamily, pow_succ,
      mul_left_comm, mul_comm]
  · intro r
    have hpow : D.dominantEigenvalue ^ r ≠ 0 := by
      exact pow_ne_zero _ D.hdominant.ne'
    simp [pom_hankel_minor_dynamics_dominant_exterior_spectrum_minor,
      pom_hankel_minor_dynamics_dominant_exterior_spectrum_shiftedHankelFamily, hpow, div_eq_mul_inv]

end Omega.POM
