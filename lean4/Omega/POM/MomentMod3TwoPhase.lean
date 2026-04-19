import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- The degree-`3` polynomial phase in the binomial basis. -/
def pomMomentDegreeThreePhase (a : Fin 4 → ℚ) (n : ℕ) : ℚ :=
  ∑ i : Fin 4, a i * Nat.choose n i

/-- The degree-`4` alternating polynomial phase in the binomial basis. -/
def pomMomentAlternatingDegreeFourPhase (b : Fin 5 → ℚ) (n : ℕ) : ℚ :=
  (-1 : ℚ) ^ n * ∑ j : Fin 5, b j * Nat.choose n j

/-- The shifted moment sequence used in the paper-facing two-phase package. -/
def pomMomentMod3ShiftedSequence (a : Fin 4 → ℚ) (b : Fin 5 → ℚ) (n : ℕ) : ℚ :=
  pomMomentDegreeThreePhase a n + pomMomentAlternatingDegreeFourPhase b n

/-- Binomial-polynomial phase of sign `σ` and degree at most `d`. -/
def IsBinomialPolynomialPhase (s : ℕ → ℚ) (σ : ℚ) (d : ℕ) : Prop :=
  ∃ coeff : Fin (d + 1) → ℚ, ∀ n, s n = σ ^ n * ∑ j : Fin (d + 1), coeff j * Nat.choose n j

private theorem pomMomentDegreeThreePhase_isPhase (a : Fin 4 → ℚ) :
    IsBinomialPolynomialPhase (pomMomentDegreeThreePhase a) 1 3 := by
  refine ⟨a, ?_⟩
  intro n
  simp [pomMomentDegreeThreePhase]

private theorem pomMomentAlternatingDegreeFourPhase_isPhase (b : Fin 5 → ℚ) :
    IsBinomialPolynomialPhase (pomMomentAlternatingDegreeFourPhase b) (-1) 4 := by
  refine ⟨b, ?_⟩
  intro n
  simp [pomMomentAlternatingDegreeFourPhase]

/-- Concrete two-phase normal form for the mod-`3` moment package: the shifted sequence splits
into a degree-`3` polynomial phase and a degree-`4` alternating polynomial phase, both written in
the binomial basis.
    prop:pom-moment-mod3-two-phase -/
theorem paper_pom_moment_mod3_two_phase (a : Fin 4 → ℚ) (b : Fin 5 → ℚ) :
    ∃ sPos sNeg : ℕ → ℚ,
      (∀ n, pomMomentMod3ShiftedSequence a b n = sPos n + sNeg n) ∧
      IsBinomialPolynomialPhase sPos 1 3 ∧
      IsBinomialPolynomialPhase sNeg (-1) 4 := by
  refine ⟨pomMomentDegreeThreePhase a, pomMomentAlternatingDegreeFourPhase b, ?_, ?_, ?_⟩
  · intro n
    simp [pomMomentMod3ShiftedSequence]
  · exact pomMomentDegreeThreePhase_isPhase a
  · exact pomMomentAlternatingDegreeFourPhase_isPhase b

end Omega.POM
