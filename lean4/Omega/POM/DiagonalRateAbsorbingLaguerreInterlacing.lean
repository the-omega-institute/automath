import Mathlib.Tactic

namespace Omega.POM

open Finset

/-- Deleted-point spectrum used for an explicit absorbing Laguerre interlacing witness. -/
def diagonalRateAbsorbingLaguerreDeletedSpectrum : Finset ℕ := {5, 8}

/-- The absorbing lag parameter `κ`. -/
def diagonalRateAbsorbingLaguerreKappa : ℝ := 1

/-- The deleted-point Laguerre polynomial attached to the secular equation
`1 / (5 - z) + 1 / (8 - z) = 1 / z`. -/
def diagonalRateAbsorbingLaguerrePolynomial (z : ℝ) : ℝ :=
  3 * z ^ 2 - 26 * z * diagonalRateAbsorbingLaguerreKappa +
    40 * diagonalRateAbsorbingLaguerreKappa

/-- The corresponding secular residual. -/
noncomputable def diagonalRateAbsorbingSecularResidual (z : ℝ) : ℝ :=
  1 / (5 - z) + 1 / (8 - z) - diagonalRateAbsorbingLaguerreKappa / z

/-- Concrete interlacing statement: the deleted-point Laguerre roots are exactly the two secular
solutions, one in each open interval cut out by `κ < 5 < 8`. -/
def diagonalRateAbsorbingLaguerreInterlacingStatement : Prop :=
  diagonalRateAbsorbingLaguerreDeletedSpectrum.card = 2 ∧
    diagonalRateAbsorbingLaguerreKappa = 1 ∧
    diagonalRateAbsorbingSecularResidual 2 = 0 ∧
    diagonalRateAbsorbingSecularResidual ((20 : ℝ) / 3) = 0 ∧
    (∀ z : ℝ,
      diagonalRateAbsorbingLaguerrePolynomial z = 0 ↔
        z = 2 ∨ z = (20 : ℝ) / 3) ∧
    (∃! z : ℝ,
      diagonalRateAbsorbingLaguerreKappa < z ∧ z < 5 ∧
        diagonalRateAbsorbingLaguerrePolynomial z = 0) ∧
    ∃! z : ℝ,
      5 < z ∧ z < 8 ∧ diagonalRateAbsorbingLaguerrePolynomial z = 0

private lemma diagonalRateAbsorbingLaguerrePolynomial_factor (z : ℝ) :
    diagonalRateAbsorbingLaguerrePolynomial z = (z - 2) * (3 * z - 20) := by
  unfold diagonalRateAbsorbingLaguerrePolynomial diagonalRateAbsorbingLaguerreKappa
  ring_nf

private lemma diagonalRateAbsorbingLaguerrePolynomial_root_iff (z : ℝ) :
    diagonalRateAbsorbingLaguerrePolynomial z = 0 ↔ z = 2 ∨ z = (20 : ℝ) / 3 := by
  rw [diagonalRateAbsorbingLaguerrePolynomial_factor]
  constructor
  · intro hz
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hz with h | h
    · left
      linarith
    · right
      linarith
  · rintro (rfl | hz)
    · norm_num [diagonalRateAbsorbingLaguerrePolynomial, diagonalRateAbsorbingLaguerreKappa]
    · subst hz
      norm_num [diagonalRateAbsorbingLaguerrePolynomial, diagonalRateAbsorbingLaguerreKappa]

/-- Paper label: `thm:pom-diagonal-rate-absorbing-laguerre-interlacing`. -/
theorem paper_pom_diagonal_rate_absorbing_laguerre_interlacing :
    diagonalRateAbsorbingLaguerreInterlacingStatement := by
  refine ⟨by native_decide, rfl, ?_, ?_, diagonalRateAbsorbingLaguerrePolynomial_root_iff, ?_, ?_⟩
  · norm_num [diagonalRateAbsorbingSecularResidual, diagonalRateAbsorbingLaguerreKappa]
  · norm_num [diagonalRateAbsorbingSecularResidual, diagonalRateAbsorbingLaguerreKappa]
  · refine ⟨2, ?_, ?_⟩
    · constructor
      · norm_num [diagonalRateAbsorbingLaguerreKappa]
      constructor
      · norm_num
      · exact (diagonalRateAbsorbingLaguerrePolynomial_root_iff 2).2 (Or.inl rfl)
    · intro z hz
      rcases hz with ⟨hzκ, hz5, hzroot⟩
      rcases (diagonalRateAbsorbingLaguerrePolynomial_root_iff z).1 hzroot with h | h
      · exact h
      · linarith
  · refine ⟨(20 : ℝ) / 3, ?_, ?_⟩
    · constructor
      · norm_num
      constructor
      · norm_num
      · exact (diagonalRateAbsorbingLaguerrePolynomial_root_iff ((20 : ℝ) / 3)).2 (Or.inr rfl)
    · intro z hz
      rcases hz with ⟨hz5, hz8, hzroot⟩
      rcases (diagonalRateAbsorbingLaguerrePolynomial_root_iff z).1 hzroot with h | h
      · linarith
      · exact h

end Omega.POM
