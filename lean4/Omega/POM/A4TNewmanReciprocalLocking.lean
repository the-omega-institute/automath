import Mathlib.Tactic
import Omega.POM.A4TNewmanShortElimination

namespace Omega.POM

/-- Rational evaluation of the Newman quadratic product. -/
def pom_a4t_newman_reciprocal_locking_Q (t x : ℚ) : ℚ :=
  (t * x + 3 * x ^ 2 - 2) * (t * x + 4 * t - 5 * x ^ 2 + 4 * x + 6)

/-- Rational cleared form of the short-elimination identity
`4 r^4 Q_t(1 / r) - r Q_t(r)`. -/
def pom_a4t_newman_reciprocal_locking_G (t r : ℚ) : ℚ :=
  4 * r ^ 4 * pom_a4t_newman_reciprocal_locking_Q t r⁻¹ -
    r * pom_a4t_newman_reciprocal_locking_Q t r

/-- Concrete critical-point data for the cleared Newman reciprocal-locking identity. -/
abbrev pom_a4t_newman_reciprocal_locking_data :=
  { p : ℚ × ℚ //
    pom_a4t_newman_reciprocal_locking_G p.1 p.2 = 0 ∧ p.2 ≠ 0 }

/-- The critical parameter. -/
def pom_a4t_newman_reciprocal_locking_t
    (D : pom_a4t_newman_reciprocal_locking_data) : ℚ :=
  D.1.1

/-- The nonzero Perron-root coordinate. -/
def pom_a4t_newman_reciprocal_locking_r
    (D : pom_a4t_newman_reciprocal_locking_data) : ℚ :=
  D.1.2

/-- Concrete reciprocal-locking statement. -/
def pom_a4t_newman_reciprocal_locking_statement
    (D : pom_a4t_newman_reciprocal_locking_data) : Prop :=
  let t : ℚ := pom_a4t_newman_reciprocal_locking_t D
  let r : ℚ := pom_a4t_newman_reciprocal_locking_r D
  pom_a4t_newman_reciprocal_locking_Q t r =
    4 * r ^ 3 * pom_a4t_newman_reciprocal_locking_Q t r⁻¹

/-- Paper label: `prop:pom-a4t-newman-reciprocal-locking`. -/
theorem paper_pom_a4t_newman_reciprocal_locking
    (D : pom_a4t_newman_reciprocal_locking_data) :
    pom_a4t_newman_reciprocal_locking_statement D := by
  obtain ⟨hG, hr⟩ := D.2
  dsimp [pom_a4t_newman_reciprocal_locking_statement,
    pom_a4t_newman_reciprocal_locking_t,
    pom_a4t_newman_reciprocal_locking_r]
  let t : ℚ := D.1.1
  let r : ℚ := D.1.2
  have hrq : r ≠ 0 := by simpa [r] using hr
  have hcleared :
      4 * r ^ 4 * pom_a4t_newman_reciprocal_locking_Q t r⁻¹ -
        r * pom_a4t_newman_reciprocal_locking_Q t r = 0 := by
    simpa [pom_a4t_newman_reciprocal_locking_G, t, r] using hG
  have hmul :
      r * pom_a4t_newman_reciprocal_locking_Q t r =
        4 * r ^ 4 * pom_a4t_newman_reciprocal_locking_Q t r⁻¹ := by
    linarith
  calc
    pom_a4t_newman_reciprocal_locking_Q t r =
        r⁻¹ * (r * pom_a4t_newman_reciprocal_locking_Q t r) := by
          field_simp [hrq]
    _ = r⁻¹ * (4 * r ^ 4 * pom_a4t_newman_reciprocal_locking_Q t r⁻¹) := by
          rw [hmul]
    _ = 4 * r ^ 3 * pom_a4t_newman_reciprocal_locking_Q t r⁻¹ := by
          field_simp [hrq]

end Omega.POM
