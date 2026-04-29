import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The elementary factor `Δ ↦ exp (-t * Δ) * Δ` is bounded above by `exp (-1) / t`, and
specializing the separation lower bound at `Δ = 1 / t` yields the optimal one-step law.
    thm:conclusion-stieltjes-prony-step-optimal-law -/
theorem paper_conclusion_stieltjes_prony_step_optimal_law
    (sep : Real -> Real -> Real) (t g0 alphaBar : Real) (ht : 0 < t) (hg0 : 0 < g0)
    (hstep : 1 / t <= Real.pi / g0)
    (hLower : forall {Delta : Real}, 0 < Delta -> Delta <= Real.pi / g0 ->
      sep t Delta >= Real.exp (-(t + alphaBar) * Delta) * (2 / Real.pi) * g0 * Delta) :
    (forall Delta : Real, 0 < Delta -> Real.exp (-t * Delta) * Delta <= Real.exp (-1) / t) ∧
      sep t (1 / t) >= (2 / (Real.pi * Real.exp 1)) * g0 * Real.exp (-alphaBar / t) / t := by
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have hone_over_t_pos : 0 < 1 / t := one_div_pos.mpr ht
  refine ⟨?_, ?_⟩
  · intro Delta hDelta
    have hmain : t * Delta ≤ Real.exp (t * Delta - 1) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        Real.add_one_le_exp (t * Delta - 1)
    have hexp_nonneg : 0 ≤ Real.exp (-t * Delta) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hmain hexp_nonneg
    have hbound : Real.exp (-t * Delta) * (t * Delta) ≤ Real.exp (-1) := by
      calc
        Real.exp (-t * Delta) * (t * Delta)
            ≤ Real.exp (-t * Delta) * Real.exp (t * Delta - 1) := hmul
        _ = Real.exp (-1) := by
              rw [← Real.exp_add]
              ring_nf
    rw [le_div_iff₀ ht]
    calc
      Real.exp (-t * Delta) * Delta * t = Real.exp (-t * Delta) * (t * Delta) := by ring
      _ ≤ Real.exp (-1) := hbound
  · have hLowerAt := hLower hone_over_t_pos hstep
    have hfactor :
        Real.exp (-(t + alphaBar) * (1 / t)) * (2 / Real.pi) * g0 * (1 / t) =
          (2 / (Real.pi * Real.exp 1)) * g0 * Real.exp (-alphaBar / t) / t := by
      have hexp :
          Real.exp (-(t + alphaBar) * (1 / t)) = Real.exp (-1) * Real.exp (-alphaBar / t) := by
        rw [show -(t + alphaBar) * (1 / t) = -1 + (-alphaBar / t) by
          field_simp [ht_ne]
          ring]
        rw [Real.exp_add]
      rw [hexp, Real.exp_neg]
      field_simp [Real.exp_pos (1 : ℝ), ht_ne]
    calc
      sep t (1 / t)
          ≥ Real.exp (-(t + alphaBar) * (1 / t)) * (2 / Real.pi) * g0 * (1 / t) := hLowerAt
      _ = (2 / (Real.pi * Real.exp 1)) * g0 * Real.exp (-alphaBar / t) / t := hfactor

end Omega.Conclusion
