import Mathlib.Tactic
import Omega.EA.TimeSpaceCommuting

namespace Omega.EA

/-- Constant row-sum of the deterministic complete-input kernel at `u = 1`. -/
def parAddU1RowSum : ℕ := 9

/-- Prime-length primitive orbit counts for the `u = 1` full-shift degeneration. -/
def parAddU1PrimitiveOrbitCount : ℕ → ℕ
  | 1 => parAddU1RowSum
  | n => (parAddU1RowSum ^ n - parAddU1RowSum) / n

/-- Paper-facing `u = 1` degeneracy package: the deterministic complete-input specialization has
    constant row sum `9`, hence fixed-point counts `9^n`, and the prime-length primitive orbit
    counts are recovered by the standard Möbius inversion formula.
    cor:par-add-u1-degeneracy -/
theorem paper_par_add_u1_degeneracy :
    parAddU1RowSum = 9 ∧
    primitiveTrace parAddU1PrimitiveOrbitCount 1 = 9 ∧
    primitiveTrace parAddU1PrimitiveOrbitCount 2 = 9 ^ 2 ∧
    primitiveTrace parAddU1PrimitiveOrbitCount 3 = 9 ^ 3 ∧
    parAddU1PrimitiveOrbitCount 2 = 36 ∧
    parAddU1PrimitiveOrbitCount 3 = 240 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [parAddU1PrimitiveOrbitCount, parAddU1RowSum] using
      primitiveTrace_one parAddU1PrimitiveOrbitCount
  · rw [primitiveTrace_prime parAddU1PrimitiveOrbitCount 2 (by decide)]
    norm_num [parAddU1PrimitiveOrbitCount, parAddU1RowSum]
  · rw [primitiveTrace_prime parAddU1PrimitiveOrbitCount 3 (by decide)]
    norm_num [parAddU1PrimitiveOrbitCount, parAddU1RowSum]
  · norm_num [parAddU1PrimitiveOrbitCount, parAddU1RowSum]
  · norm_num [parAddU1PrimitiveOrbitCount, parAddU1RowSum]

end Omega.EA
