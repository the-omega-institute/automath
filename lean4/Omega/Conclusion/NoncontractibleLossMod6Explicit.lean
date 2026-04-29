import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The maximal contractible fiber count `D_m` used in the mod-6 phase diagram. -/
def noncontractibleMainFiberCount (m : ℕ) : ℕ :=
  if m % 2 = 0 then Nat.fib (m / 2 + 2) else 2 * Nat.fib ((m - 1) / 2 + 1)

/-- The denominator-layer count `D_m^(2)` appearing in the odd noncontractible phases. -/
def noncontractibleSecondFiberCount (m : ℕ) : ℕ :=
  2 * Nat.fib ((m - 1) / 2 + 1) - Nat.fib ((m - 1) / 2 - 4)

/-- The denominator-layer count `D_m^(3)` appearing in the third noncontractible phase. -/
def noncontractibleThirdFiberCount (m : ℕ) : ℕ :=
  if m % 2 = 0 then Nat.fib (m / 2 + 2) - Nat.fib (m / 2 - 3)
  else 2 * Nat.fib ((m - 1) / 2 + 1) - Nat.fib ((m - 1) / 2 - 4) - Nat.fib ((m - 1) / 2 - 8)

/-- The restricted noncontractible fiber count `\widetilde D_m`, packaged by residue class mod `6`.
-/
def noncontractibleFiberCount (m : ℕ) : ℕ :=
  match m % 6 with
  | 0 => noncontractibleMainFiberCount m
  | 1 => noncontractibleSecondFiberCount m
  | 2 => noncontractibleThirdFiberCount m
  | 3 => noncontractibleThirdFiberCount m
  | 4 => noncontractibleMainFiberCount m
  | 5 => noncontractibleSecondFiberCount m
  | _ => 0

/-- The noncontractible loss is the logarithm of the restricted fiber count. -/
noncomputable def noncontractibleLoss (m : ℕ) : ℝ :=
  Real.log (noncontractibleFiberCount m)

/-- Concrete statement recording the parity formulas and the equivalent mod-`6` phase diagram for
the noncontractible loss package. -/
def NoncontractibleLossMod6ExplicitStatement : Prop :=
  (∀ k : ℕ,
      noncontractibleLoss (2 * k) =
        if k % 3 = 1 then Real.log ((Nat.fib (k + 2) : ℝ) - Nat.fib (k - 3))
        else Real.log (Nat.fib (k + 2))) ∧
    (∀ k : ℕ,
      noncontractibleLoss (2 * k + 1) =
        if k % 3 = 1
        then Real.log ((2 * Nat.fib (k + 1) : ℝ) - Nat.fib (k - 4) - Nat.fib (k - 8))
        else Real.log ((2 * Nat.fib (k + 1) : ℝ) - Nat.fib (k - 4))) ∧
    (∀ m : ℕ,
      noncontractibleLoss m =
        if m % 6 = 0 ∨ m % 6 = 4 then Real.log (noncontractibleMainFiberCount m)
        else if m % 6 = 1 ∨ m % 6 = 5 then Real.log (noncontractibleSecondFiberCount m)
        else Real.log (noncontractibleThirdFiberCount m))

/-- Paper label: `thm:conclusion-noncontractible-loss-mod6-explicit`.
Case-splitting by `m mod 6` rewrites the noncontractible loss as the logarithm of the appropriate
restricted fiber count, and the parity formulas are the corresponding closed Fibonacci forms. -/
theorem paper_conclusion_noncontractible_loss_mod6_explicit :
    NoncontractibleLossMod6ExplicitStatement := by
  refine ⟨?_, ?_, ?_⟩
  · intro k
    have hklt : k % 3 < 3 := Nat.mod_lt _ (by omega)
    interval_cases hk : k % 3
    · have hmod : (2 * k) % 6 = 0 := by omega
      simp [noncontractibleLoss, noncontractibleFiberCount, noncontractibleMainFiberCount, hmod]
    · have hmod : (2 * k) % 6 = 2 := by omega
      simp [noncontractibleLoss, noncontractibleFiberCount, noncontractibleThirdFiberCount, hmod]
      have hle : Nat.fib (k - 3) ≤ Nat.fib (k + 2) := Nat.fib_mono (by omega)
      rw [Nat.cast_sub hle]
    · have hmod : (2 * k) % 6 = 4 := by omega
      simp [noncontractibleLoss, noncontractibleFiberCount, noncontractibleMainFiberCount, hmod]
  · intro k
    have hklt : k % 3 < 3 := Nat.mod_lt _ (by omega)
    interval_cases hk : k % 3
    · have hmod : (2 * k + 1) % 6 = 1 := by omega
      simp [noncontractibleLoss, noncontractibleFiberCount, noncontractibleSecondFiberCount, hmod]
      have hle : Nat.fib (k - 4) ≤ 2 * Nat.fib (k + 1) := by
        have hmono : Nat.fib (k - 4) ≤ Nat.fib (k + 1) := Nat.fib_mono (by omega)
        omega
      rw [Nat.cast_sub hle, Nat.cast_mul]
      norm_num
    · have hmod : (2 * k + 1) % 6 = 3 := by omega
      simp [noncontractibleLoss, noncontractibleFiberCount, noncontractibleThirdFiberCount, hmod]
      have hle₁ : Nat.fib (k - 4) ≤ 2 * Nat.fib (k + 1) := by
        have hmono : Nat.fib (k - 4) ≤ Nat.fib (k + 1) := Nat.fib_mono (by omega)
        omega
      have hsum : Nat.fib (k - 8) + Nat.fib (k - 4) ≤ 2 * Nat.fib (k + 1) := by
        have hmono₁ : Nat.fib (k - 8) ≤ Nat.fib (k + 1) := Nat.fib_mono (by omega)
        have hmono₂ : Nat.fib (k - 4) ≤ Nat.fib (k + 1) := Nat.fib_mono (by omega)
        omega
      have hle₂ : Nat.fib (k - 8) ≤ 2 * Nat.fib (k + 1) - Nat.fib (k - 4) := by
        omega
      rw [Nat.cast_sub hle₂, Nat.cast_sub hle₁, Nat.cast_mul]
      norm_num
    · have hmod : (2 * k + 1) % 6 = 5 := by omega
      simp [noncontractibleLoss, noncontractibleFiberCount, noncontractibleSecondFiberCount, hmod]
      have hle : Nat.fib (k - 4) ≤ 2 * Nat.fib (k + 1) := by
        have hmono : Nat.fib (k - 4) ≤ Nat.fib (k + 1) := Nat.fib_mono (by omega)
        omega
      rw [Nat.cast_sub hle, Nat.cast_mul]
      norm_num
  · intro m
    have hmlt : m % 6 < 6 := Nat.mod_lt _ (by omega)
    interval_cases hm : m % 6
    · simp [noncontractibleLoss, noncontractibleFiberCount, hm]
    · simp [noncontractibleLoss, noncontractibleFiberCount, hm]
    · simp [noncontractibleLoss, noncontractibleFiberCount, hm]
    · simp [noncontractibleLoss, noncontractibleFiberCount, hm]
    · simp [noncontractibleLoss, noncontractibleFiberCount, hm]
    · simp [noncontractibleLoss, noncontractibleFiberCount, hm]

end Omega.Conclusion
