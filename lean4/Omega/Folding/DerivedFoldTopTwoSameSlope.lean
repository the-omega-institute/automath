import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Folding.FiberSpectrum

namespace Omega

/-- The top two fibers in regular Fold differ only by an explicit positive multiplicative
correction on each parity branch: the top layer has the Fibonacci closed forms, the second layer
subtracts the stable forbidden-pair gap, and taking logs isolates the correction term exactly. -/
theorem paper_derived_fold_top_two_same_slope
    (two_step : ∀ m, 6 ≤ m →
      Omega.X.maxFiberMultiplicity m =
        Omega.X.maxFiberMultiplicity (m - 2) + Omega.X.maxFiberMultiplicity (m - 4))
    (forbidden_even : ∀ k : Nat, 5 ≤ k →
      cNthMaxFiber (2 * k) 1 =
        Omega.X.maxFiberMultiplicity (2 * k) - Nat.fib (k - 4))
    (forbidden_odd : ∀ k : Nat, 5 ≤ k →
      cNthMaxFiber (2 * k + 1) 1 =
        Omega.X.maxFiberMultiplicity (2 * k + 1) - Nat.fib (k - 4)) :
    (∀ k : Nat, 5 ≤ k → Omega.X.maxFiberMultiplicity (2 * k) = Nat.fib (k + 2)) ∧
    (∀ k : Nat, 5 ≤ k → Omega.X.maxFiberMultiplicity (2 * k + 1) = 2 * Nat.fib (k + 1)) ∧
    (∀ k : Nat, 5 ≤ k → cNthMaxFiber (2 * k) 1 = Nat.fib (k + 2) - Nat.fib (k - 4)) ∧
    (∀ k : Nat, 5 ≤ k → cNthMaxFiber (2 * k + 1) 1 = 2 * Nat.fib (k + 1) - Nat.fib (k - 4)) ∧
    (∀ k : Nat, 5 ≤ k →
      Real.log (cNthMaxFiber (2 * k) 1 : ℝ) -
        Real.log (Omega.X.maxFiberMultiplicity (2 * k) : ℝ) =
          Real.log (1 - (Nat.fib (k - 4) : ℝ) / Nat.fib (k + 2))) ∧
    (∀ k : Nat, 5 ≤ k →
      Real.log (cNthMaxFiber (2 * k + 1) 1 : ℝ) -
        Real.log (Omega.X.maxFiberMultiplicity (2 * k + 1) : ℝ) =
          Real.log (1 - (Nat.fib (k - 4) : ℝ) / (2 * Nat.fib (k + 1)))) := by
  rcases paper_pom_second_max_fiber_closed_form two_step forbidden_even forbidden_odd with
    ⟨_, _, _, hSecondEven, hSecondOdd⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    exact Omega.X.maxFiberMultiplicity_even_of_two_step two_step k (by omega)
  · intro k hk
    exact Omega.X.maxFiberMultiplicity_odd_of_two_step two_step k (by omega)
  · intro k hk
    exact hSecondEven k hk
  · intro k hk
    exact hSecondOdd k hk
  · intro k hk
    rw [hSecondEven k hk, Omega.X.maxFiberMultiplicity_even_of_two_step two_step k (by omega)]
    have htop_pos_nat : 0 < Nat.fib (k + 2) := Nat.fib_pos.mpr (by omega)
    have htop_ne : (Nat.fib (k + 2) : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt htop_pos_nat)
    have hgap_le : Nat.fib (k - 4) ≤ Nat.fib (k + 2) := Nat.fib_mono (by omega)
    have hsecond_pos : 0 < (Nat.fib (k + 2) - Nat.fib (k - 4) : ℕ) := by
      have hmono : Nat.fib (k - 4) ≤ Nat.fib (k + 1) := Nat.fib_mono (by omega)
      have hpos : 0 < Nat.fib k := Nat.fib_pos.mpr (by omega)
      rw [Nat.fib_add_two]
      omega
    have hlog :
        Real.log ((Nat.fib (k + 2) - Nat.fib (k - 4) : ℕ) : ℝ) - Real.log (Nat.fib (k + 2) : ℝ) =
          Real.log (((Nat.fib (k + 2) - Nat.fib (k - 4) : ℕ) : ℝ) / Nat.fib (k + 2)) := by
      symm
      exact Real.log_div (ne_of_gt (by exact_mod_cast hsecond_pos)) htop_ne
    rw [hlog]
    rw [Nat.cast_sub hgap_le]
    field_simp [htop_ne]
  · intro k hk
    rw [hSecondOdd k hk, Omega.X.maxFiberMultiplicity_odd_of_two_step two_step k (by omega)]
    have htop_pos_nat : 0 < 2 * Nat.fib (k + 1) := by
      have hfib : 0 < Nat.fib (k + 1) := Nat.fib_pos.mpr (by omega)
      omega
    have htop_ne : ((2 * Nat.fib (k + 1) : Nat) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt htop_pos_nat)
    have hgap_le : Nat.fib (k - 4) ≤ 2 * Nat.fib (k + 1) := by
      have hmono : Nat.fib (k - 4) ≤ Nat.fib (k + 1) := Nat.fib_mono (by omega)
      omega
    have hsecond_pos : 0 < (2 * Nat.fib (k + 1) - Nat.fib (k - 4) : ℕ) := by
      have hmono : Nat.fib (k - 4) ≤ Nat.fib (k + 1) := Nat.fib_mono (by omega)
      have hfib : 0 < Nat.fib (k + 1) := Nat.fib_pos.mpr (by omega)
      omega
    have hlog :
        Real.log ((2 * Nat.fib (k + 1) - Nat.fib (k - 4) : ℕ) : ℝ) -
            Real.log ((2 * Nat.fib (k + 1) : ℕ) : ℝ) =
          Real.log (((2 * Nat.fib (k + 1) - Nat.fib (k - 4) : ℕ) : ℝ) /
            ((2 * Nat.fib (k + 1) : ℕ) : ℝ)) := by
      symm
      have hsecond_ne : (((2 * Nat.fib (k + 1) - Nat.fib (k - 4) : ℕ) : ℝ) ≠ 0) := by
        exact_mod_cast (Nat.ne_of_gt hsecond_pos)
      exact Real.log_div hsecond_ne htop_ne
    rw [hlog]
    rw [Nat.cast_sub hgap_le, Nat.cast_mul]
    norm_num
    field_simp [htop_ne]

end Omega
