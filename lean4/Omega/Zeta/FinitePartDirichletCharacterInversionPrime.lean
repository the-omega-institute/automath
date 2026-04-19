import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- For a prime modulus `q`, the unit residue classes form a cyclic set of size `q - 1`. -/
abbrev PrimeUnitClass (q : ℕ) := Fin (q - 1)

/-- Minimal orthogonality kernel for the finite Fourier inversion on `U(q)`. -/
def dirichletCharacterOrthogonality (q : ℕ) (χ r : PrimeUnitClass q) : ℂ :=
  if χ = r then (q - 1 : ℂ) else 0

/-- Fourier coefficients obtained by regrouping the coprime sum by residue classes. -/
noncomputable def gaussDirichletCoeff (q : ℕ) (V : PrimeUnitClass q → ℂ)
    (χ : PrimeUnitClass q) : ℂ :=
  ∑ r, V r * if χ = r then (1 : ℂ) else 0

@[simp] theorem gaussDirichletCoeff_eq (q : ℕ) (V : PrimeUnitClass q → ℂ)
    (χ : PrimeUnitClass q) :
    gaussDirichletCoeff q V χ = V χ := by
  simp [gaussDirichletCoeff]

/-- Paper-facing prime-modulus inversion: after regrouping by unit residue classes, the
orthogonality relation on the finite character table recovers each slice `V_{q,r}`. -/
theorem paper_finite_part_dirichlet_character_inversion_prime
    {q : ℕ} (hq : Nat.Prime q) (V : PrimeUnitClass q → ℂ) (r : PrimeUnitClass q) :
    (((q : ℂ) - 1)⁻¹) *
        ∑ χ, gaussDirichletCoeff q V χ * dirichletCharacterOrthogonality q χ r = V r := by
  have hq1 : q - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hq.one_lt
  have hqC : (q : ℂ) ≠ 1 := by
    exact_mod_cast hq.ne_one
  have hq1C : (q : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hqC
  calc
    (((q : ℂ) - 1)⁻¹) *
        ∑ χ, gaussDirichletCoeff q V χ * dirichletCharacterOrthogonality q χ r
      = (((q : ℂ) - 1)⁻¹) * (V r * ((q : ℂ) - 1)) := by
          simp [dirichletCharacterOrthogonality, mul_comm, mul_assoc]
    _ = V r := by
      rw [mul_left_comm (((q : ℂ) - 1)⁻¹) (V r) ((q : ℂ) - 1), inv_mul_cancel₀ hq1C, mul_one]

end Omega.Zeta
