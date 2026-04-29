import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Fibonacci
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

open Filter
open scoped Topology goldenRatio

namespace Omega.Folding

/-- The concrete density attached to the minimum-degeneracy sector. -/
noncomputable def foldBinMinsectorDensity (sectorCard totalCard : ℕ) : ℝ :=
  sectorCard / totalCard

private theorem tendsto_fib_div_fib_add_two :
    Tendsto (fun m : ℕ => (Nat.fib m : ℝ) / Nat.fib (m + 2)) atTop
      (𝓝 ((φ : ℝ)⁻¹ * φ⁻¹)) := by
  have h₁ :
      Tendsto (fun m : ℕ => (Nat.fib m : ℝ) / Nat.fib (m + 1)) atTop (𝓝 (-ψ)) :=
    tendsto_fib_div_fib_succ_atTop
  have h₂ :
      Tendsto (fun m : ℕ => (Nat.fib (m + 1) : ℝ) / Nat.fib (m + 2)) atTop (𝓝 (-ψ)) := by
    simpa [Nat.add_assoc] using
      (tendsto_fib_div_fib_succ_atTop.comp (tendsto_add_atTop_nat 1))
  have hmul := h₁.mul h₂
  convert hmul using 1
  · ext m
    have hfib : (Nat.fib (m + 1) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (Nat.fib_pos.mpr (Nat.succ_pos _))
    field_simp [hfib]
  · have hpsi : (-ψ : ℝ) = φ⁻¹ := by
      simpa using (Real.inv_goldenRatio : φ⁻¹ = (-ψ : ℝ)).symm
    rw [hpsi]

/-- If the minimum sector cardinality rewrites as `|X_{m-2}| = F_m` and the ambient stable-word
count is `|X_m| = F_{m+2}`, then the density is exactly `F_m / F_{m+2}` and converges to
`φ^{-2}`.
    cor:fold-bin-minsector-density-phi-minus2 -/
theorem paper_fold_bin_minsector_density_phi_minus2
    (sectorCard totalCard : ℕ → ℕ)
    (hsector : ∀ m : ℕ, sectorCard m = Nat.fib m)
    (htotal : ∀ m : ℕ, totalCard m = Nat.fib (m + 2)) :
    (∀ m : ℕ, foldBinMinsectorDensity (sectorCard m) (totalCard m) =
      (Nat.fib m : ℝ) / Nat.fib (m + 2)) ∧
      Tendsto (fun m : ℕ => foldBinMinsectorDensity (sectorCard m) (totalCard m)) atTop
        (𝓝 ((φ : ℝ)⁻¹ * φ⁻¹)) := by
  refine ⟨?_, ?_⟩
  · intro m
    simp [foldBinMinsectorDensity, hsector m, htotal m]
  · have hrewrite :
        (fun m : ℕ => foldBinMinsectorDensity (sectorCard m) (totalCard m)) =
          fun m : ℕ => (Nat.fib m : ℝ) / Nat.fib (m + 2) := by
        funext m
        simp [foldBinMinsectorDensity, hsector m, htotal m]
    rw [hrewrite]
    exact tendsto_fib_div_fib_add_two

end Omega.Folding
