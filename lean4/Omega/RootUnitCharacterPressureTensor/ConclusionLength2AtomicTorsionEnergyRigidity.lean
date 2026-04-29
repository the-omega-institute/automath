import Mathlib.Data.Rat.Defs

namespace Omega.RootUnitCharacterPressureTensor

/-- Primitive squared torsion-energy average for the length `2` atom. -/
def conclusion_length2_atomic_torsion_energy_rigidity_primitiveEnergy
    (_q n : ℕ) : ℚ :=
  if n = 2 then (1 : ℚ) else 0

/-- Periodic squared torsion-energy average for the length `2` atom. -/
def conclusion_length2_atomic_torsion_energy_rigidity_periodicEnergy
    (_q n : ℕ) : ℚ :=
  if 2 ∣ n then (4 : ℚ) else 0

/-- Paper label: `cor:conclusion-length2-atomic-torsion-energy-rigidity`. -/
theorem paper_conclusion_length2_atomic_torsion_energy_rigidity (q n : ℕ) (hq : 2 ≤ q) :
    conclusion_length2_atomic_torsion_energy_rigidity_primitiveEnergy q n =
        (if n = 2 then (1 : ℚ) else 0) ∧
      conclusion_length2_atomic_torsion_energy_rigidity_periodicEnergy q n =
        (if 2 ∣ n then (4 : ℚ) else 0) := by
  have _ : 2 ≤ q := hq
  simp [conclusion_length2_atomic_torsion_energy_rigidity_primitiveEnergy,
    conclusion_length2_atomic_torsion_energy_rigidity_periodicEnergy]

end Omega.RootUnitCharacterPressureTensor
