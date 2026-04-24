import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Conclusion.NoncontractibleLossMod6Explicit

namespace Omega.POM

theorem paper_derived_max_noncontractible_fiber_defect_constants :
    (∀ k : Nat,
      9 ≤ k →
        (Omega.Conclusion.noncontractibleFiberCount (2 * k) : ℚ) /
            Omega.Conclusion.noncontractibleMainFiberCount (2 * k) =
          if k % 3 = 1 then 1 - (Nat.fib (k - 3) : ℚ) / Nat.fib (k + 2) else 1) ∧
      (∀ k : Nat,
        8 ≤ k →
          (Omega.Conclusion.noncontractibleFiberCount (2 * k + 1) : ℚ) /
              Omega.Conclusion.noncontractibleMainFiberCount (2 * k + 1) =
            if k % 3 = 1 then
              1 - ((Nat.fib (k - 4) + Nat.fib (k - 8) : ℚ) / (2 * Nat.fib (k + 1)))
            else
              1 - (Nat.fib (k - 4) : ℚ) / (2 * Nat.fib (k + 1))) := by
  refine ⟨?_, ?_⟩
  · intro k hk
    have hklt : k % 3 < 3 := Nat.mod_lt _ (by omega)
    interval_cases hmod3 : k % 3
    · have hm6 : (2 * k) % 6 = 0 := by omega
      have hpos : (Nat.fib (k + 2) : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Nat.fib_pos.mpr (by omega)))
      simp [Omega.Conclusion.noncontractibleFiberCount, Omega.Conclusion.noncontractibleMainFiberCount,
        hm6]
    · have hm6 : (2 * k) % 6 = 2 := by omega
      have hle : Nat.fib (k - 3) ≤ Nat.fib (k + 2) := Nat.fib_mono (by omega)
      have hpos : (Nat.fib (k + 2) : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Nat.fib_pos.mpr (by omega)))
      simp [Omega.Conclusion.noncontractibleFiberCount, Omega.Conclusion.noncontractibleMainFiberCount,
        Omega.Conclusion.noncontractibleThirdFiberCount, hm6]
      rw [Nat.cast_sub hle]
      field_simp [hpos]
    · have hm6 : (2 * k) % 6 = 4 := by omega
      have hpos : (Nat.fib (k + 2) : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Nat.fib_pos.mpr (by omega)))
      simp [Omega.Conclusion.noncontractibleFiberCount, Omega.Conclusion.noncontractibleMainFiberCount,
        hm6]
  · intro k hk
    have hklt : k % 3 < 3 := Nat.mod_lt _ (by omega)
    interval_cases hmod3 : k % 3
    · have hm6 : (2 * k + 1) % 6 = 1 := by omega
      have hle : Nat.fib (k - 4) ≤ 2 * Nat.fib (k + 1) := by
        have hmono : Nat.fib (k - 4) ≤ Nat.fib (k + 1) := Nat.fib_mono (by omega)
        omega
      have hpos : ((2 * Nat.fib (k + 1) : Nat) : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (by
          have hfib : 0 < Nat.fib (k + 1) := Nat.fib_pos.mpr (by omega)
          omega))
      simp [Omega.Conclusion.noncontractibleFiberCount, Omega.Conclusion.noncontractibleMainFiberCount,
        Omega.Conclusion.noncontractibleSecondFiberCount, hm6]
      rw [Nat.cast_sub hle, Nat.cast_mul]
      norm_num
      field_simp [hpos]
    · have hm6 : (2 * k + 1) % 6 = 3 := by omega
      have hle₁ : Nat.fib (k - 4) ≤ 2 * Nat.fib (k + 1) := by
        have hmono : Nat.fib (k - 4) ≤ Nat.fib (k + 1) := Nat.fib_mono (by omega)
        omega
      have hsum : Nat.fib (k - 8) + Nat.fib (k - 4) ≤ 2 * Nat.fib (k + 1) := by
        have hmono₁ : Nat.fib (k - 8) ≤ Nat.fib (k + 1) := Nat.fib_mono (by omega)
        have hmono₂ : Nat.fib (k - 4) ≤ Nat.fib (k + 1) := Nat.fib_mono (by omega)
        omega
      have hle₂ : Nat.fib (k - 8) ≤ 2 * Nat.fib (k + 1) - Nat.fib (k - 4) := by omega
      have hpos : ((2 * Nat.fib (k + 1) : Nat) : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (by
          have hfib : 0 < Nat.fib (k + 1) := Nat.fib_pos.mpr (by omega)
          omega))
      simp [Omega.Conclusion.noncontractibleFiberCount, Omega.Conclusion.noncontractibleMainFiberCount,
        Omega.Conclusion.noncontractibleThirdFiberCount, hm6]
      rw [Nat.cast_sub hle₂, Nat.cast_sub hle₁, Nat.cast_mul]
      norm_num
      ring_nf
      field_simp [hpos]
    · have hm6 : (2 * k + 1) % 6 = 5 := by omega
      have hle : Nat.fib (k - 4) ≤ 2 * Nat.fib (k + 1) := by
        have hmono : Nat.fib (k - 4) ≤ Nat.fib (k + 1) := Nat.fib_mono (by omega)
        omega
      have hpos : ((2 * Nat.fib (k + 1) : Nat) : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (by
          have hfib : 0 < Nat.fib (k + 1) := Nat.fib_pos.mpr (by omega)
          omega))
      simp [Omega.Conclusion.noncontractibleFiberCount, Omega.Conclusion.noncontractibleMainFiberCount,
        Omega.Conclusion.noncontractibleSecondFiberCount, hm6]
      rw [Nat.cast_sub hle, Nat.cast_mul]
      norm_num
      field_simp [hpos]

end Omega.POM
