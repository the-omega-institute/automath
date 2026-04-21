import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.SyncKernelWeighted.CharacterPhaseCyclotomicElimination
import Omega.SyncKernelWeighted.IharaArtinFactorization

namespace Omega.SyncKernelWeighted

open Matrix
open Polynomial

/-- The normalized characteristic polynomial of the explicit boundary channel. -/
noncomputable def conclusion75NormalizedCharacteristicPolynomial : Polynomial ℤ :=
  X ^ 2 - 1

/-- The cyclotomic factor corresponding to the unit root `-1`. -/
noncomputable def conclusion75CyclotomicFactor : Polynomial ℤ :=
  X + 1

/-- The `r = 2` compression data for the even-power polynomial `X² - 1 = -1 + U`. -/
noncomputable def conclusion75CyclotomicData : CharacterPhaseCyclotomicEliminationData where
  r := 2
  hr := by decide
  compressedCoeff
    | 0 => -1
    | 1 => 1
    | _ => 0

/-- The explicit normalized determinant contains the cyclotomic factor `X + 1`. -/
def conclusion75HasCyclotomicFactor : Prop :=
  ∃ Q : Polynomial ℤ,
    conclusion75NormalizedCharacteristicPolynomial = conclusion75CyclotomicFactor * Q

/-- The same normalized determinant has a unit-modulus boundary eigenvalue at `-1`. -/
def conclusion75UnitModulusBoundaryEigenvalue : Prop :=
  IsRoot (Polynomial.map (Int.castRingHom ℂ) conclusion75NormalizedCharacteristicPolynomial)
      (-1 : ℂ) ∧
    ‖(-1 : ℂ)‖ = 1

/-- In the explicit resonant specialization, Ihara--Artin factorization holds, the cyclotomic
elimination package compresses the normalized determinant to even powers, and having the
cyclotomic factor `X + 1` is equivalent to the presence of the unit-modulus boundary eigenvalue
`-1`.
    thm:conclusion75-ihara-cyclotomic-factor-classification -/
theorem paper_conclusion75_ihara_cyclotomic_factor_classification :
    Matrix.det (1 - (1 : ℤ) • regularRepresentationHashimotoBlock 1 (-1)) =
      Matrix.det (1 - (1 : ℤ) • trivialTwistedHashimotoBlock 1) *
        Matrix.det (1 - (1 : ℤ) • irreducibleTwistedHashimotoBlock (-1)) ∧
    conclusion75CyclotomicData.muInvariant ∧
    conclusion75CyclotomicData.existsCompression ∧
    conclusion75CyclotomicData.uniqueCompression ∧
    (conclusion75HasCyclotomicFactor ↔ conclusion75UnitModulusBoundaryEigenvalue) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa using paper_ihara_artin_factorization (t := (1 : ℤ)) (u := 1) (v := -1)
  · exact (paper_character_phase_cyclotomic_elimination conclusion75CyclotomicData).1
  · exact (paper_character_phase_cyclotomic_elimination conclusion75CyclotomicData).2.1
  · exact (paper_character_phase_cyclotomic_elimination conclusion75CyclotomicData).2.2
  · constructor
    · intro _
      refine ⟨?_, by norm_num⟩
      simp [conclusion75NormalizedCharacteristicPolynomial]
    · intro _
      refine ⟨X - 1, ?_⟩
      simp [conclusion75NormalizedCharacteristicPolynomial, conclusion75CyclotomicFactor]
      ring

end Omega.SyncKernelWeighted
