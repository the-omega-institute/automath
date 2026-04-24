import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Folding.Entropy

open Filter
open scoped Topology

namespace Omega.POM

/-- The Rényi-`2` near-uniform collision ratio inherits its exponential rate from the Fibonacci
growth of `|X_m| = F_{m+2}` and the exponential rate of the collision sum `S2`. -/
theorem paper_pom_renyi2_near_uniform
    (R S2 : ℕ → ℝ) (r2 : ℝ)
    (hR : ∀ m, R m = ((Nat.fib (m + 2) : ℝ) * S2 m) / (4 : ℝ) ^ m)
    (hS2_pos : ∀ m, 0 < S2 m)
    (hr2 : 0 < r2)
    (hS2 :
      Tendsto (fun m : ℕ => Real.log (S2 m) / (m : ℝ)) atTop (nhds (Real.log r2))) :
    Tendsto (fun m : ℕ => Real.log (R m) / (m : ℝ)) atTop
      (nhds (Real.log (Real.goldenRatio * r2 / 4))) := by
  have hmain :
      Tendsto
        (fun m : ℕ =>
          Real.log ((Nat.fib (m + 2) : ℝ)) / (m : ℝ) + Real.log (S2 m) / (m : ℝ) -
            Real.log (4 : ℝ))
        atTop
        (nhds (Real.log Real.goldenRatio + Real.log r2 - Real.log (4 : ℝ))) := by
    simpa [sub_eq_add_neg] using
      (Omega.Entropy.topological_entropy_eq_log_phi.add hS2).add
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => -Real.log (4 : ℝ)) atTop (nhds (-Real.log (4 : ℝ))))
  have hEq :
      (fun m : ℕ => Real.log (R m) / (m : ℝ)) =ᶠ[atTop]
        fun m : ℕ =>
          Real.log ((Nat.fib (m + 2) : ℝ)) / (m : ℝ) + Real.log (S2 m) / (m : ℝ) -
            Real.log (4 : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    have hm_pos : 0 < m := hm
    have hm_ne : (m : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hm_pos)
    have hfib_pos : 0 < (Nat.fib (m + 2) : ℝ) := by
      exact_mod_cast Nat.fib_pos.mpr (by omega)
    have hpow_ne : (4 : ℝ) ^ m ≠ 0 := by positivity
    rw [hR m]
    rw [Real.log_div (mul_ne_zero hfib_pos.ne' (hS2_pos m).ne') hpow_ne]
    rw [Real.log_mul hfib_pos.ne' (hS2_pos m).ne', Real.log_pow]
    field_simp [hm_ne]
  have hlimit :
      Tendsto (fun m : ℕ => Real.log (R m) / (m : ℝ)) atTop
        (nhds (Real.log Real.goldenRatio + Real.log r2 - Real.log (4 : ℝ))) :=
    hmain.congr' hEq.symm
  have htarget :
      Real.log Real.goldenRatio + Real.log r2 - Real.log (4 : ℝ) =
        Real.log (Real.goldenRatio * r2 / 4) := by
    rw [Real.log_div (show Real.goldenRatio * r2 ≠ 0 by positivity) (by norm_num : (4 : ℝ) ≠ 0)]
    rw [Real.log_mul (ne_of_gt Real.goldenRatio_pos) (ne_of_gt hr2)]
  simpa [htarget] using hlimit

end Omega.POM
