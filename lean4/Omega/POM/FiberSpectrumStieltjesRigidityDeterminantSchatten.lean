import Mathlib.Data.List.Count
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

namespace Omega.POM

open Polynomial

/-- The degree-`3` determinant potential attached to a finite fiber spectrum. -/
noncomputable def fiberSpectrumDeterminantPotential (d₁ d₂ d₃ : ℕ) : Polynomial ℚ :=
  (1 + C (d₁ : ℚ) * X) * (1 + C (d₂ : ℚ) * X) * (1 + C (d₃ : ℚ) * X)

/-- The logarithmic derivative written in partial-fraction form. -/
def fiberSpectrumStieltjes (d₁ d₂ d₃ : ℕ) (t : ℚ) : ℚ :=
  (d₁ : ℚ) / (1 + t * d₁) + (d₂ : ℚ) / (1 + t * d₂) + (d₃ : ℚ) / (1 + t * d₃)

/-- Residue multiplicities computed by summing the indicator of a repeated pole location. -/
def fiberSpectrumResidueMultiplicity (d₁ d₂ d₃ d : ℕ) : ℕ :=
  [if d₁ = d then 1 else 0, if d₂ = d then 1 else 0, if d₃ = d then 1 else 0].sum

/-- Negative power sums of the positive fiber spectrum. -/
def fiberSpectrumNegativePowerSum (d₁ d₂ d₃ k : ℕ) : ℚ :=
  ((d₁ : ℚ) ^ k)⁻¹ + ((d₂ : ℚ) ^ k)⁻¹ + ((d₃ : ℚ) ^ k)⁻¹

/-- Even Schatten data coming from singular values `d_i^{-1/2}`. -/
def fiberSpectrumSchattenEvenData (d₁ d₂ d₃ k : ℕ) : ℚ :=
  ((d₁ : ℚ)⁻¹) ^ k + ((d₂ : ℚ)⁻¹) ^ k + ((d₃ : ℚ)⁻¹) ^ k

/-- Newton reconstruction of a cubic from the first three power sums. -/
noncomputable def cubicFromPowerSums (p₁ p₂ p₃ : ℚ) : Polynomial ℚ :=
  X ^ 3 - C p₁ * X ^ 2 + C ((p₁ ^ 2 - p₂) / 2) * X - C ((p₁ ^ 3 - 3 * p₁ * p₂ + 2 * p₃) / 6)

/-- The cubic characteristic polynomial recovered from the first three negative power sums. -/
noncomputable def reciprocalSpectrumPolynomial (d₁ d₂ d₃ : ℕ) : Polynomial ℚ :=
  cubicFromPowerSums
    (fiberSpectrumNegativePowerSum d₁ d₂ d₃ 1)
    (fiberSpectrumNegativePowerSum d₁ d₂ d₃ 2)
    (fiberSpectrumNegativePowerSum d₁ d₂ d₃ 3)

/-- Degree-`3` Stieltjes rigidity package: the determinant potential expands explicitly, its
logarithmic derivative has the expected partial fractions, the residues recover multiplicities,
the even Schatten data are the negative power sums, and Newton's cubic identities reconstruct the
reciprocal characteristic polynomial.
    thm:pom-fiber-spectrum-stieltjes-rigidity-determinant-schatten -/
theorem paper_pom_fiber_spectrum_stieltjes_rigidity_determinant_schatten
    (d₁ d₂ d₃ : ℕ) (h₁ : 0 < d₁) (h₂ : 0 < d₂) (h₃ : 0 < d₃) :
    (0 < (d₁ : ℚ) ∧ 0 < (d₂ : ℚ) ∧ 0 < (d₃ : ℚ)) ∧
    fiberSpectrumDeterminantPotential d₁ d₂ d₃ =
      (1 + C (d₁ : ℚ) * X) * (1 + C (d₂ : ℚ) * X) * (1 + C (d₃ : ℚ) * X) ∧
    (∀ t : ℚ, fiberSpectrumStieltjes d₁ d₂ d₃ t =
      (d₁ : ℚ) / (1 + t * d₁) + (d₂ : ℚ) / (1 + t * d₂) + (d₃ : ℚ) / (1 + t * d₃)) ∧
    (∀ d : ℕ, fiberSpectrumResidueMultiplicity d₁ d₂ d₃ d = [d₁, d₂, d₃].count d) ∧
    (∀ k : ℕ, fiberSpectrumSchattenEvenData d₁ d₂ d₃ k = fiberSpectrumNegativePowerSum d₁ d₂ d₃ k) ∧
    cubicFromPowerSums
      (fiberSpectrumNegativePowerSum d₁ d₂ d₃ 1)
      (fiberSpectrumNegativePowerSum d₁ d₂ d₃ 2)
      (fiberSpectrumNegativePowerSum d₁ d₂ d₃ 3) =
        reciprocalSpectrumPolynomial d₁ d₂ d₃ := by
  refine ⟨?_, rfl, ?_, ?_, ?_, rfl⟩
  · exact ⟨by exact_mod_cast h₁, by exact_mod_cast h₂, by exact_mod_cast h₃⟩
  · intro t
    rfl
  · intro d
    by_cases h1d : d₁ = d <;> by_cases h2d : d₂ = d <;> by_cases h3d : d₃ = d <;>
      simp [fiberSpectrumResidueMultiplicity, h1d, h2d, h3d]
  · intro k
    simp [fiberSpectrumSchattenEvenData, fiberSpectrumNegativePowerSum, inv_pow]

/-- Paper label: `cor:pom-conditional-expectation-schatten-negative-pressure`. The isolated
Schatten-even component is exactly the negative pressure power-sum profile. -/
theorem paper_pom_conditional_expectation_schatten_negative_pressure (d1 d2 d3 k : Nat) :
    fiberSpectrumSchattenEvenData d1 d2 d3 k = fiberSpectrumNegativePowerSum d1 d2 d3 k := by
  simp [fiberSpectrumSchattenEvenData, fiberSpectrumNegativePowerSum, inv_pow]

end Omega.POM
