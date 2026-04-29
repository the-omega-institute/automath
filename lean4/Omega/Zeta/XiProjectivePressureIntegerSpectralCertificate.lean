import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

namespace Omega.Zeta

open Polynomial

/-- Integer pressure sample attached to the integer spectral root. -/
noncomputable def xi_projective_pressure_integer_spectral_certificate_pressure (r : ℤ) : ℝ :=
  Real.log |(r : ℝ)|

/-- The finite integer characteristic polynomial used by the spectral certificate. -/
noncomputable def xi_projective_pressure_integer_spectral_certificate_charpoly {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) : Polynomial ℤ :=
  A.charpoly

/-- Concrete finite spectral certificate: the integer matrix has a monic characteristic
polynomial, the displayed root is a characteristic root, and the pressure sample is its logarithmic
modulus. -/
def xi_projective_pressure_integer_spectral_certificate_finite_spectral_certificate {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) (r : ℤ) : Prop :=
  (xi_projective_pressure_integer_spectral_certificate_charpoly A).Monic ∧
    (xi_projective_pressure_integer_spectral_certificate_charpoly A).eval r = 0 ∧
      xi_projective_pressure_integer_spectral_certificate_pressure r = Real.log |(r : ℝ)|

/-- Paper label: `thm:xi-projective-pressure-integer-spectral-certificate`.
For any finite integer moment-kernel matrix and any displayed integer characteristic root, the
characteristic polynomial itself is the finite monic spectral certificate for the integer pressure
sample. -/
theorem paper_xi_projective_pressure_integer_spectral_certificate {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) (r : ℤ)
    (hroot :
      (xi_projective_pressure_integer_spectral_certificate_charpoly A).eval r = 0) :
    xi_projective_pressure_integer_spectral_certificate_finite_spectral_certificate A r := by
  refine ⟨?_, hroot, rfl⟩
  exact Matrix.charpoly_monic A

end Omega.Zeta
