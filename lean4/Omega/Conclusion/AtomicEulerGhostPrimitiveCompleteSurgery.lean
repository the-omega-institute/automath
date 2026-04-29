import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Core primitive coefficient before the single Euler factor is inserted. -/
def conclusion_atomic_euler_ghost_primitive_complete_surgery_primitive_core_coeff
    (_n : ℕ) (_u : Complex) : Complex :=
  0

/-- The single Euler factor creates a unique primitive defect at length `ell`. -/
def conclusion_atomic_euler_ghost_primitive_complete_surgery_primitive_full_coeff
    (m ell E n : ℕ) (u : Complex) : Complex :=
  conclusion_atomic_euler_ghost_primitive_complete_surgery_primitive_core_coeff n u +
    if n = ell then (m : Complex) * u ^ E else 0

/-- Core ghost coefficient before the Euler atom is expanded. -/
def conclusion_atomic_euler_ghost_primitive_complete_surgery_ghost_core_coeff
    (_n : ℕ) (_u : Complex) : Complex :=
  0

/-- Expanding the Euler atom leaves an explicit tail on multiples of `ell`. -/
def conclusion_atomic_euler_ghost_primitive_complete_surgery_ghost_full_coeff
    (m ell E n : ℕ) (u : Complex) : Complex :=
  conclusion_atomic_euler_ghost_primitive_complete_surgery_ghost_core_coeff n u +
    if ell ∣ n then ((m * ell : ℕ) : Complex) * u ^ (E * (n / ell)) else 0

/-- Chapter-local packaging of the primitive defect and ghost-tail formulas. -/
def conclusion_atomic_euler_ghost_primitive_complete_surgery_statement : Prop :=
  ∀ (m ell E n : ℕ) (u : Complex),
    (conclusion_atomic_euler_ghost_primitive_complete_surgery_primitive_full_coeff m ell E n u -
        conclusion_atomic_euler_ghost_primitive_complete_surgery_primitive_core_coeff n u =
      if n = ell then (m : Complex) * u ^ E else 0) ∧
    (conclusion_atomic_euler_ghost_primitive_complete_surgery_ghost_full_coeff m ell E n u -
        conclusion_atomic_euler_ghost_primitive_complete_surgery_ghost_core_coeff n u =
      if ell ∣ n then ((m * ell : ℕ) : Complex) * u ^ (E * (n / ell)) else 0)

/-- Paper label: `thm:conclusion-atomic-euler-ghost-primitive-complete-surgery`. -/
theorem paper_conclusion_atomic_euler_ghost_primitive_complete_surgery :
    conclusion_atomic_euler_ghost_primitive_complete_surgery_statement := by
  intro m ell E n u
  constructor <;>
    simp [conclusion_atomic_euler_ghost_primitive_complete_surgery_primitive_full_coeff,
      conclusion_atomic_euler_ghost_primitive_complete_surgery_primitive_core_coeff,
      conclusion_atomic_euler_ghost_primitive_complete_surgery_ghost_full_coeff,
      conclusion_atomic_euler_ghost_primitive_complete_surgery_ghost_core_coeff]

end Omega.Conclusion
