import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open Finset
open scoped BigOperators

/-- Paper label:
`thm:conclusion-principal-shadow-mismatch-ladder-jacobi-coupling-inversion`. The mismatch ladder
product formula can be inverted one coupling at a time by dividing `Delta 1` by `u0`, and for
later levels by dividing consecutive ladder values. -/
theorem paper_conclusion_principal_shadow_mismatch_ladder_jacobi_coupling_inversion
    (u0 : ℝ) (Delta alpha : ℕ → ℝ) (hu0 : u0 ≠ 0) (halpha : ∀ n ≥ 1, 0 < alpha n)
    (hDelta0 : Delta 0 = u0)
    (hDelta : ∀ n ≥ 1, Delta n = u0 * Finset.prod (Finset.Icc 1 n) (fun i => (alpha i)^2)) :
    alpha 1 ^ 2 = Delta 1 / u0 ∧ ∀ n ≥ 2, alpha n ^ 2 = Delta n / Delta (n - 1) := by
  have hDelta1 : Delta 1 = u0 * alpha 1 ^ 2 := by
    simpa using hDelta 1 (by omega)
  refine ⟨?_, ?_⟩
  · exact (eq_div_iff hu0).2 <| by simpa [mul_comm] using hDelta1.symm
  · intro n hn
    have hn1 : 1 ≤ n := by omega
    have hnprev : 1 ≤ n - 1 := by omega
    have hDelta_prev :
        Delta (n - 1) = u0 * Finset.prod (Finset.Icc 1 (n - 1)) (fun i => (alpha i)^2) := by
      exact hDelta (n - 1) hnprev
    have hDelta_n :
        Delta n =
          u0 * Finset.prod (Finset.Icc 1 (n - 1)) (fun i => (alpha i)^2) * alpha n ^ 2 := by
      have hmain := hDelta n hn1
      rw [show n = (n - 1) + 1 by omega,
        Finset.prod_Icc_succ_top (show 1 ≤ (n - 1) + 1 by omega)] at hmain
      simpa [show n - 1 + 1 = n by omega, mul_assoc] using hmain
    have hprod_pos :
        0 < Finset.prod (Finset.Icc 1 (n - 1)) (fun i => (alpha i)^2) := by
      refine Finset.prod_pos ?_
      intro i hi
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      have hai : 0 < alpha i := halpha i hi1
      nlinarith
    have hDelta_prev_ne : Delta (n - 1) ≠ 0 := by
      rw [hDelta_prev]
      exact mul_ne_zero hu0 hprod_pos.ne'
    have hstep : Delta n = Delta (n - 1) * alpha n ^ 2 := by
      calc
        Delta n = u0 * Finset.prod (Finset.Icc 1 (n - 1)) (fun i => (alpha i)^2) * alpha n ^ 2 :=
          hDelta_n
        _ = Delta (n - 1) * alpha n ^ 2 := by
          rw [hDelta_prev]
    exact (eq_div_iff hDelta_prev_ne).2 <| by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hstep.symm

end Omega.Conclusion
