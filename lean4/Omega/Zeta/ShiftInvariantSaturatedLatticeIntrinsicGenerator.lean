import Mathlib.Tactic
import Omega.Zeta.ShiftInvariantSaturatedLatticePrincipalIdeal

namespace Omega.Zeta

open Polynomial

/-- Paper-facing intrinsic-generator package for the concrete saturated shift-invariant tail
lattice. -/
def xi_saturated_shift_invariant_lattice_intrinsic_generator_statement : Prop :=
  ∀ n m : ℕ, m ≤ n →
    ShiftInvariant n (tailLattice n m) ∧
      Saturated (tailLattice n m) ∧
      principalIdealLattice n (X ^ m : ℤ[X]) = tailLattice n m ∧
      (∀ P : ℤ[X],
        P.Monic →
          P.natDegree = m →
            principalIdealLattice n P = tailLattice n m →
              P = X ^ m) ∧
      ∀ j : ℕ, coeffVector n ((X ^ j) * (X ^ m) : ℤ[X]) ∈ tailLattice n m

/-- The shifted powers of the intrinsic generator all lie in the tail lattice. -/
lemma xi_saturated_shift_invariant_lattice_intrinsic_generator_shifted_family
    (n m j : ℕ) (hmn : m ≤ n) :
    coeffVector n ((X ^ j) * (X ^ m) : ℤ[X]) ∈ tailLattice n m := by
  have hmem :
      coeffVector n ((X ^ j) * (X ^ m) : ℤ[X]) ∈ principalIdealLattice n (X ^ m : ℤ[X]) := by
    exact ⟨X ^ j, rfl⟩
  simpa [principalIdealLattice_X_pow_eq_tailLattice n m hmn] using hmem

/-- Paper label: `prop:xi-saturated-shift-invariant-lattice-intrinsic-generator`. -/
theorem paper_xi_saturated_shift_invariant_lattice_intrinsic_generator :
    xi_saturated_shift_invariant_lattice_intrinsic_generator_statement := by
  intro n m hmn
  refine ⟨tailLattice_shiftInvariant n m, tailLattice_saturated n m,
    principalIdealLattice_X_pow_eq_tailLattice n m hmn, ?_, ?_⟩
  · intro P hmonic hdeg hP
    exact monic_generator_of_tailLattice_eq_X_pow n m hmn hmonic hdeg hP
  · intro j
    exact xi_saturated_shift_invariant_lattice_intrinsic_generator_shifted_family n m j hmn

end Omega.Zeta
