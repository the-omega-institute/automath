import Mathlib.Data.Set.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete read-visible symmetry data: a state space together with its visible readout. -/
structure ReadVisibleSymmetryData (Omega Y : Type*) [DecidableEq Omega] where
  read : Omega → Y

/-- A permutation is a read symmetry when it preserves the visible readout on every state. -/
def ReadVisibleSymmetryData.isReadSymmetry
    {Omega Y : Type*} [DecidableEq Omega]
    (D : ReadVisibleSymmetryData Omega Y) (σ : Equiv.Perm Omega) : Prop :=
  ∀ omega : Omega, D.read (σ omega) = D.read omega

/-- The orbit of a state under all read-preserving permutations. -/
def ReadVisibleSymmetryData.readOrbit
    {Omega Y : Type*} [DecidableEq Omega]
    (D : ReadVisibleSymmetryData Omega Y) (omega : Omega) : Set Omega :=
  {omega' | ∃ σ : Equiv.Perm Omega, D.isReadSymmetry σ ∧ σ omega = omega'}

/-- The read-preserving orbit of a state is exactly its read fiber.
    prop:xi-read-fiber-orbits -/
theorem paper_xi_read_fiber_orbits
    {Omega Y : Type*} [DecidableEq Omega]
    (D : ReadVisibleSymmetryData Omega Y) (omega : Omega) :
    D.readOrbit omega = {omega' | D.read omega' = D.read omega} := by
  ext omega'
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact hσ omega
  · intro hread
    refine ⟨Equiv.swap omega omega', ?_, ?_⟩
    · intro x
      by_cases hx : x = omega
      · subst hx
        simpa [Equiv.swap_apply_left] using hread
      · by_cases hx' : x = omega'
        · subst hx'
          simpa [Equiv.swap_apply_right] using hread.symm
        · rw [Equiv.swap_apply_of_ne_of_ne hx hx']
    · simp [Equiv.swap_apply_left]

end Omega.Zeta
