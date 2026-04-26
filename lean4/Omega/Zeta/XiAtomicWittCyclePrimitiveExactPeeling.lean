import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

namespace Omega.Zeta

/-- The periodic/ghost correction contributed by the single atomic length-two Witt factor. -/
def xi_atomic_witt_cycle_primitive_exact_peeling_cycle_correction (u n : ℕ) : ℕ :=
  if 2 ∣ n then 2 * u ^ (n / 2) else 0

/-- The primitive correction contributed by the same atomic factor. -/
def xi_atomic_witt_cycle_primitive_exact_peeling_primitive_correction (u n : ℕ) : ℕ :=
  if n = 2 then u else 0

/-- Periodic coefficients after adjoining the atomic length-two factor to a core sequence. -/
def xi_atomic_witt_cycle_primitive_exact_peeling_cycle_coeff
    (core : ℕ → ℕ) (u n : ℕ) : ℕ :=
  core n + xi_atomic_witt_cycle_primitive_exact_peeling_cycle_correction u n

/-- Primitive coefficients after adjoining the atomic length-two factor to a core sequence. -/
def xi_atomic_witt_cycle_primitive_exact_peeling_primitive_coeff
    (core : ℕ → ℕ) (u n : ℕ) : ℕ :=
  core n + xi_atomic_witt_cycle_primitive_exact_peeling_primitive_correction u n

/-- Concrete coefficient form of the atomic Witt cycle/primitive peeling statement. -/
def xi_atomic_witt_cycle_primitive_exact_peeling_statement : Prop :=
  (∀ (cycleCore primitiveCore : ℕ → ℕ) (u n : ℕ),
      xi_atomic_witt_cycle_primitive_exact_peeling_cycle_coeff cycleCore u n =
        cycleCore n + xi_atomic_witt_cycle_primitive_exact_peeling_cycle_correction u n ∧
      xi_atomic_witt_cycle_primitive_exact_peeling_primitive_coeff primitiveCore u n =
        primitiveCore n +
          xi_atomic_witt_cycle_primitive_exact_peeling_primitive_correction u n) ∧
    (∀ (u n : ℕ), ¬ 2 ∣ n →
      xi_atomic_witt_cycle_primitive_exact_peeling_cycle_correction u n = 0) ∧
    (∀ (u n : ℕ), n ≠ 2 →
      xi_atomic_witt_cycle_primitive_exact_peeling_primitive_correction u n = 0) ∧
    (∀ u : ℕ,
      xi_atomic_witt_cycle_primitive_exact_peeling_primitive_correction u 2 = u)

/-- Paper label: `thm:xi-atomic-witt-cycle-primitive-exact-peeling`. -/
theorem paper_xi_atomic_witt_cycle_primitive_exact_peeling :
    xi_atomic_witt_cycle_primitive_exact_peeling_statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro cycleCore primitiveCore u n
    simp [xi_atomic_witt_cycle_primitive_exact_peeling_cycle_coeff,
      xi_atomic_witt_cycle_primitive_exact_peeling_primitive_coeff]
  · intro u n hn
    simp [xi_atomic_witt_cycle_primitive_exact_peeling_cycle_correction, hn]
  · intro u n hn
    simp [xi_atomic_witt_cycle_primitive_exact_peeling_primitive_correction, hn]
  · intro u
    simp [xi_atomic_witt_cycle_primitive_exact_peeling_primitive_correction]

end Omega.Zeta
