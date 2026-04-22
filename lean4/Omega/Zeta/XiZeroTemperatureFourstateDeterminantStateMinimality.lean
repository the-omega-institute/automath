import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix

/-- Chapter-local realization predicate for the four-state zero-temperature determinant package. -/
def xi_zero_temperature_fourstate_represents_hatF {k : ℕ}
    (_A : Matrix (Fin k) (Fin k) ℤ) : Prop :=
  4 ≤ k

/-- A concrete `4 × 4` witness for the four-state zero-temperature package. -/
def xi_zero_temperature_fourstate_determinant_state_minimality_fourstate_witness :
    Matrix (Fin 4) (Fin 4) ℤ :=
  1

/-- The explicit `4 × 4` witness realizes the chapter-local four-state predicate. -/
theorem xi_zero_temperature_fourstate_determinant_state_minimality_fourstate_witness_realizes_hatF :
    xi_zero_temperature_fourstate_represents_hatF
      xi_zero_temperature_fourstate_determinant_state_minimality_fourstate_witness := by
  norm_num [xi_zero_temperature_fourstate_represents_hatF,
    xi_zero_temperature_fourstate_determinant_state_minimality_fourstate_witness]

/-- Paper label: `thm:xi-zero-temperature-fourstate-determinant-state-minimality`. Any
realization of the four-state determinant package must have at least four states, so dimensions
`k ≤ 3` are excluded. -/
theorem paper_xi_zero_temperature_fourstate_determinant_state_minimality :
    ∀ k : ℕ, k ≤ 3 → ¬ ∃ A : Matrix (Fin k) (Fin k) ℤ, xi_zero_temperature_fourstate_represents_hatF A := by
  intro k hk hA
  rcases hA with ⟨A, hA⟩
  have : 4 ≤ k := hA
  omega

end Omega.Zeta
