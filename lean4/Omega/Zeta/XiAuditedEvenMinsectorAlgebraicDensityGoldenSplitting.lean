import Omega.Folding.Entropy
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.Zeta

/-- Paper label: `thm:xi-audited-even-minsector-algebraic-density-golden-splitting`. -/
theorem paper_xi_audited_even_minsector_algebraic_density_golden_splitting
    (minSector total : ℕ → ℕ)
    (hmin : ∀ m : ℕ, minSector m = Nat.fib m)
    (htotal : ∀ m : ℕ, total m = Nat.fib (m + 2)) :
    (∀ m : ℕ, (minSector m : ℝ) / total m = (Nat.fib m : ℝ) / Nat.fib (m + 2)) ∧
      Tendsto (fun m : ℕ => (minSector m : ℝ) / total m) atTop
        (𝓝 ((Real.goldenRatio : ℝ)⁻¹ ^ 2)) := by
  refine ⟨?_, ?_⟩
  · intro m
    simp [hmin m, htotal m]
  · have h₁ :
        Tendsto (fun m : ℕ => (Nat.fib m : ℝ) / Nat.fib (m + 1)) atTop
          (𝓝 (Real.goldenRatio⁻¹ : ℝ)) := by
      rw [Real.inv_goldenRatio]
      simpa using tendsto_fib_div_fib_succ_atTop
    have h₂ :
        Tendsto (fun m : ℕ => (Nat.fib (m + 1) : ℝ) / Nat.fib (m + 2)) atTop
          (𝓝 (Real.goldenRatio⁻¹ : ℝ)) := by
      have h := tendsto_fib_div_fib_succ_atTop.comp (tendsto_add_atTop_nat (1 : ℕ))
      rw [Real.inv_goldenRatio]
      simpa [Nat.add_assoc] using h
    have hprod :
        Tendsto
          (fun m : ℕ =>
            ((Nat.fib m : ℝ) / Nat.fib (m + 1)) *
              ((Nat.fib (m + 1) : ℝ) / Nat.fib (m + 2)))
          atTop (𝓝 ((Real.goldenRatio⁻¹ : ℝ) ^ 2)) := by
      simpa [pow_two] using h₁.mul h₂
    refine Tendsto.congr' ?_ hprod
    filter_upwards [Filter.Eventually.of_forall fun _ => True.intro] with m _
    have hfib : (Nat.fib (m + 1) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (Nat.fib_pos.mpr (Nat.succ_pos m))
    calc
      ((Nat.fib m : ℝ) / Nat.fib (m + 1)) *
            ((Nat.fib (m + 1) : ℝ) / Nat.fib (m + 2)) =
          (Nat.fib m : ℝ) / Nat.fib (m + 2) := by
        field_simp [hfib]
      _ = (minSector m : ℝ) / total m := by
        simp [hmin m, htotal m]

end Omega.Zeta
