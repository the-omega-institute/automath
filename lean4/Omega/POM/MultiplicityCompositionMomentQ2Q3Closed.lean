import Mathlib.Tactic

namespace Omega.POM

/-- Numerator of the `q = 2` multiplicity-composition moment generating function. -/
def pom_multiplicity_composition_moment_q2_q3_closed_q2_num (t : ℚ) : ℚ :=
  (1 + t) * (t ^ 2 - 3 * t + 1)

/-- Denominator of the `q = 2` multiplicity-composition moment generating function. -/
def pom_multiplicity_composition_moment_q2_q3_closed_q2_den (t : ℚ) : ℚ :=
  1 - 6 * t - 3 * t ^ 2 + 2 * t ^ 3

/-- Closed rational form of the `q = 2` moment generating function. -/
def pom_multiplicity_composition_moment_q2_q3_closed_q2_gf (t : ℚ) : ℚ :=
  pom_multiplicity_composition_moment_q2_q3_closed_q2_num t /
    pom_multiplicity_composition_moment_q2_q3_closed_q2_den t

/-- Characteristic polynomial read from the reciprocal `q = 2` denominator. -/
def pom_multiplicity_composition_moment_q2_q3_closed_q2_char (lam : ℚ) : ℚ :=
  lam ^ 3 - 6 * lam ^ 2 - 3 * lam + 2

/-- Numerator of the `q = 3` multiplicity-composition moment generating function. -/
def pom_multiplicity_composition_moment_q2_q3_closed_q3_num (t : ℚ) : ℚ :=
  (t ^ 2 - t - 1) * (t ^ 2 + 4 * t - 1)

/-- Denominator of the `q = 3` multiplicity-composition moment generating function. -/
def pom_multiplicity_composition_moment_q2_q3_closed_q3_den (t : ℚ) : ℚ :=
  1 - 11 * t - 9 * t ^ 2 + 7 * t ^ 3 + 2 * t ^ 4

/-- Closed rational form of the `q = 3` moment generating function. -/
def pom_multiplicity_composition_moment_q2_q3_closed_q3_gf (t : ℚ) : ℚ :=
  pom_multiplicity_composition_moment_q2_q3_closed_q3_num t /
    pom_multiplicity_composition_moment_q2_q3_closed_q3_den t

/-- Characteristic polynomial read from the reciprocal `q = 3` denominator. -/
def pom_multiplicity_composition_moment_q2_q3_closed_q3_char (lam : ℚ) : ℚ :=
  lam ^ 4 - 11 * lam ^ 3 - 9 * lam ^ 2 + 7 * lam + 2

/-- Paper label: `cor:pom-multiplicity-composition-moment-q2-q3-closed`.

The closed forms are recorded as rational generating-function identities, and the characteristic
polynomials are the reciprocal denominator polynomials obtained by coefficient comparison. -/
theorem paper_pom_multiplicity_composition_moment_q2_q3_closed :
    (∀ t : ℚ,
      pom_multiplicity_composition_moment_q2_q3_closed_q2_den t ≠ 0 →
        pom_multiplicity_composition_moment_q2_q3_closed_q2_den t *
          pom_multiplicity_composition_moment_q2_q3_closed_q2_gf t =
            pom_multiplicity_composition_moment_q2_q3_closed_q2_num t) ∧
    (∀ lam : ℚ,
      lam ≠ 0 →
        lam ^ 3 *
          pom_multiplicity_composition_moment_q2_q3_closed_q2_den lam⁻¹ =
            pom_multiplicity_composition_moment_q2_q3_closed_q2_char lam) ∧
    (∀ t : ℚ,
      pom_multiplicity_composition_moment_q2_q3_closed_q3_den t ≠ 0 →
        pom_multiplicity_composition_moment_q2_q3_closed_q3_den t *
          pom_multiplicity_composition_moment_q2_q3_closed_q3_gf t =
            pom_multiplicity_composition_moment_q2_q3_closed_q3_num t) ∧
    (∀ lam : ℚ,
      lam ≠ 0 →
        lam ^ 4 *
          pom_multiplicity_composition_moment_q2_q3_closed_q3_den lam⁻¹ =
            pom_multiplicity_composition_moment_q2_q3_closed_q3_char lam) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t hden
    unfold pom_multiplicity_composition_moment_q2_q3_closed_q2_gf
    field_simp [hden]
  · intro lam hlam
    unfold pom_multiplicity_composition_moment_q2_q3_closed_q2_den
      pom_multiplicity_composition_moment_q2_q3_closed_q2_char
    field_simp [hlam]
  · intro t hden
    unfold pom_multiplicity_composition_moment_q2_q3_closed_q3_gf
    field_simp [hden]
  · intro lam hlam
    unfold pom_multiplicity_composition_moment_q2_q3_closed_q3_den
      pom_multiplicity_composition_moment_q2_q3_closed_q3_char
    field_simp [hlam]

end Omega.POM
