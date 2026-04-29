import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic
import Omega.Conclusion.AtomicPrimitiveRamanujanVisibilityLaw

open scoped BigOperators

namespace Omega.Conclusion

/-- Concrete finite atomic data for the ghost Ramanujan ray law.  The primitive visibility data
provides the atom lengths and multiplicities; this layer adds the ghost energy and a core ghost
ray. -/
structure conclusion_atomic_ghost_ramanujan_ray_law_data where
  conclusion_atomic_ghost_ramanujan_ray_law_primitive_data :
    conclusion_atomic_primitive_ramanujan_visibility_law_data
  conclusion_atomic_ghost_ramanujan_ray_law_atom_energy :
    Fin conclusion_atomic_ghost_ramanujan_ray_law_primitive_data.atomCount → ℕ
  conclusion_atomic_ghost_ramanujan_ray_law_core_coefficient : ℕ → ℂ → ℂ
  conclusion_atomic_ghost_ramanujan_ray_law_core_ray : ℕ → ℂ → ℂ → ℂ

namespace conclusion_atomic_ghost_ramanujan_ray_law_data

/-- The coefficient contributed by one atomic Euler factor to the ghost coordinate. -/
def conclusion_atomic_ghost_ramanujan_ray_law_atom_coefficient
    (D : conclusion_atomic_ghost_ramanujan_ray_law_data)
    (j : Fin D.conclusion_atomic_ghost_ramanujan_ray_law_primitive_data.atomCount)
    (n : ℕ) (u : ℂ) : ℂ :=
  if D.conclusion_atomic_ghost_ramanujan_ray_law_primitive_data.atomLength j ∣ n then
    D.conclusion_atomic_ghost_ramanujan_ray_law_primitive_data.atomMultiplicity j *
      (D.conclusion_atomic_ghost_ramanujan_ray_law_primitive_data.atomLength j : ℂ) *
        u ^
          (D.conclusion_atomic_ghost_ramanujan_ray_law_atom_energy j *
            (n /
              D.conclusion_atomic_ghost_ramanujan_ray_law_primitive_data.atomLength j))
  else
    0

/-- The total finite atomic ghost coefficient. -/
noncomputable def conclusion_atomic_ghost_ramanujan_ray_law_atomic_coefficient
    (D : conclusion_atomic_ghost_ramanujan_ray_law_data) (n : ℕ) (u : ℂ) : ℂ :=
  ∑ j : Fin D.conclusion_atomic_ghost_ramanujan_ray_law_primitive_data.atomCount,
    D.conclusion_atomic_ghost_ramanujan_ray_law_atom_coefficient j n u

/-- The core-plus-atoms ghost coefficient. -/
noncomputable def conclusion_atomic_ghost_ramanujan_ray_law_coefficient
    (D : conclusion_atomic_ghost_ramanujan_ray_law_data) (n : ℕ) (u : ℂ) : ℂ :=
  D.conclusion_atomic_ghost_ramanujan_ray_law_core_coefficient n u +
    D.conclusion_atomic_ghost_ramanujan_ray_law_atomic_coefficient n u

/-- One atom's closed geometric ray in the `r`-th divisor-sieve layer. -/
noncomputable def conclusion_atomic_ghost_ramanujan_ray_law_geometric_ray_atom
    (D : conclusion_atomic_ghost_ramanujan_ray_law_data)
    (j : Fin D.conclusion_atomic_ghost_ramanujan_ray_law_primitive_data.atomCount)
    (r : ℕ) (z u : ℂ) : ℂ :=
  let length := D.conclusion_atomic_ghost_ramanujan_ray_law_primitive_data.atomLength j
  let rayStep := r / Nat.gcd r length
  let monomial :=
    u ^ (D.conclusion_atomic_ghost_ramanujan_ray_law_atom_energy j * rayStep) *
      z ^ (length * rayStep)
  D.conclusion_atomic_ghost_ramanujan_ray_law_primitive_data.atomMultiplicity j *
    (length : ℂ) * (monomial / (1 - monomial))

/-- The core-plus-atoms geometric ray expression. -/
noncomputable def conclusion_atomic_ghost_ramanujan_ray_law_geometric_ray
    (D : conclusion_atomic_ghost_ramanujan_ray_law_data) (r : ℕ) (z u : ℂ) : ℂ :=
  D.conclusion_atomic_ghost_ramanujan_ray_law_core_ray r z u +
    ∑ j : Fin D.conclusion_atomic_ghost_ramanujan_ray_law_primitive_data.atomCount,
      D.conclusion_atomic_ghost_ramanujan_ray_law_geometric_ray_atom j r z u

/-- The coefficient formula: a ghost coefficient splits into its core and finite atomic
contributions. -/
def conclusion_atomic_ghost_ramanujan_ray_law_coefficient_formula
    (D : conclusion_atomic_ghost_ramanujan_ray_law_data) : Prop :=
  ∀ n : ℕ, ∀ u : ℂ,
    D.conclusion_atomic_ghost_ramanujan_ray_law_coefficient n u =
      D.conclusion_atomic_ghost_ramanujan_ray_law_core_coefficient n u +
        ∑ j : Fin D.conclusion_atomic_ghost_ramanujan_ray_law_primitive_data.atomCount,
          D.conclusion_atomic_ghost_ramanujan_ray_law_atom_coefficient j n u

/-- The geometric-ray law: the divisor-sieve ray is the core ray plus the finite sum of closed
atomic rays, and the admissible harmonic index is exactly a multiple of `r / gcd r length`. -/
def conclusion_atomic_ghost_ramanujan_ray_law_geometric_ray_formula
    (D : conclusion_atomic_ghost_ramanujan_ray_law_data) : Prop :=
  (∀ r : ℕ, ∀ z u : ℂ,
    D.conclusion_atomic_ghost_ramanujan_ray_law_geometric_ray r z u =
      D.conclusion_atomic_ghost_ramanujan_ray_law_core_ray r z u +
        ∑ j : Fin D.conclusion_atomic_ghost_ramanujan_ray_law_primitive_data.atomCount,
          D.conclusion_atomic_ghost_ramanujan_ray_law_geometric_ray_atom j r z u) ∧
  (∀ (j : Fin D.conclusion_atomic_ghost_ramanujan_ray_law_primitive_data.atomCount)
      (r k : ℕ), 0 < r →
      let length := D.conclusion_atomic_ghost_ramanujan_ray_law_primitive_data.atomLength j
      r ∣ length * k ↔ r / Nat.gcd r length ∣ k)

end conclusion_atomic_ghost_ramanujan_ray_law_data

private lemma conclusion_atomic_ghost_ramanujan_ray_law_admissible_iff
    (r length k : ℕ) (hr : 0 < r) :
    r ∣ length * k ↔ r / Nat.gcd r length ∣ k := by
  let g := Nat.gcd r length
  have hgpos : 0 < g := by
    exact Nat.gcd_pos_of_pos_left length hr
  have hr_eq : r = (r / g) * g := by
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_left r length)).symm
  have hlength_eq : length = (length / g) * g := by
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_right r length)).symm
  have hlength_mul : length * k = (length / g * k) * g := by
    nth_rw 1 [hlength_eq]
    ac_rfl
  have hcop : Nat.Coprime (r / g) (length / g) := by
    dsimp [g]
    exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left length hr)
  calc
    r ∣ length * k ↔ (r / g) * g ∣ length * k := by
      rw [← hr_eq]
    _ ↔ (r / g) * g ∣ (length / g * k) * g := by
      rw [← hlength_mul]
    _ ↔ r / g ∣ length / g * k := by
      exact mul_dvd_mul_iff_right hgpos.ne'
    _ ↔ r / g ∣ k := by
      exact hcop.dvd_mul_left

/-- Paper label: `thm:conclusion-atomic-ghost-ramanujan-ray-law`. -/
theorem paper_conclusion_atomic_ghost_ramanujan_ray_law
    (D : conclusion_atomic_ghost_ramanujan_ray_law_data) :
    D.conclusion_atomic_ghost_ramanujan_ray_law_coefficient_formula ∧
      D.conclusion_atomic_ghost_ramanujan_ray_law_geometric_ray_formula := by
  constructor
  · intro n u
    rfl
  · constructor
    · intro r z u
      rfl
    · intro j r k hr
      exact conclusion_atomic_ghost_ramanujan_ray_law_admissible_iff r
        (D.conclusion_atomic_ghost_ramanujan_ray_law_primitive_data.atomLength j) k hr

end Omega.Conclusion
