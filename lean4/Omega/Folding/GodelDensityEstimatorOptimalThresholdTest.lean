import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

namespace Omega.Folding

private theorem weighted_log_lt_zero
    (a x y : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y)
    (havg : a * x + (1 - a) * y = 1) :
    a * Real.log x + (1 - a) * Real.log y < 0 := by
  have hb0 : 0 < 1 - a := by linarith
  have hab : a + (1 - a) = 1 := by ring
  have hconc := strictConcaveOn_log_Ioi.2 hx hy hxy ha0 hb0 hab
  simpa [havg, Real.log_one, smul_eq_mul] using hconc

/-- The explicit threshold `η*` from the paper lies strictly between `p₀` and `p₁`, and it is the
unique balance point where the Bernoulli KL exponents against `p₀` and `p₁` coincide.
    cor:fold-godel-density-estimator-optimal-threshold-test -/
theorem paper_fold_godel_density_estimator_optimal_threshold_test (p0 p1 : ℝ)
    (hp : 0 < p0 ∧ p0 < p1 ∧ p1 < 1) :
    let etaStar :=
      Real.log ((1 - p0) / (1 - p1)) /
        Real.log ((p1 * (1 - p0)) / (p0 * (1 - p1)))
    p0 < etaStar ∧ etaStar < p1 ∧
      (etaStar * Real.log (etaStar / p0) +
          (1 - etaStar) * Real.log ((1 - etaStar) / (1 - p0))) =
        (etaStar * Real.log (etaStar / p1) +
          (1 - etaStar) * Real.log ((1 - etaStar) / (1 - p1))) := by
  rcases hp with ⟨hp0, hp0p1, hp1lt1⟩
  have hp1 : 0 < p1 := lt_trans hp0 hp0p1
  have h1mp0 : 0 < 1 - p0 := by linarith
  have h1mp1 : 0 < 1 - p1 := by linarith
  dsimp
  set η : ℝ :=
    Real.log ((1 - p0) / (1 - p1)) /
      Real.log ((p1 * (1 - p0)) / (p0 * (1 - p1))) with hη
  set N : ℝ := Real.log ((1 - p0) / (1 - p1))
  set D : ℝ := Real.log ((p1 * (1 - p0)) / (p0 * (1 - p1)))
  have hη_def : η = N / D := by
    simpa [N, D] using hη
  have hratio_pos : 0 < (p1 * (1 - p0)) / (p0 * (1 - p1)) := by positivity
  have hratio_gt : 1 < (p1 * (1 - p0)) / (p0 * (1 - p1)) := by
    have hden_pos : 0 < p0 * (1 - p1) := mul_pos hp0 h1mp1
    refine (one_lt_div hden_pos).2 ?_
    nlinarith
  have hD_pos : 0 < D := by
    change 0 < Real.log ((p1 * (1 - p0)) / (p0 * (1 - p1)))
    exact Real.log_pos hratio_gt
  have hD_ne : D ≠ 0 := ne_of_gt hD_pos
  have hN_pos : 0 < N := by
    change 0 < Real.log ((1 - p0) / (1 - p1))
    have hratioN_gt : 1 < (1 - p0) / (1 - p1) := by
      exact (one_lt_div h1mp1).2 (by linarith)
    exact Real.log_pos hratioN_gt
  have hD_split : D = Real.log (p1 / p0) + N := by
    have hratio_decomp :
        (p1 * (1 - p0)) / (p0 * (1 - p1)) = (p1 / p0) * ((1 - p0) / (1 - p1)) := by
      field_simp [hp0.ne', h1mp1.ne']
    change Real.log ((p1 * (1 - p0)) / (p0 * (1 - p1))) = Real.log (p1 / p0) + N
    rw [show N = Real.log ((1 - p0) / (1 - p1)) by rfl]
    rw [hratio_decomp, Real.log_mul (by positivity) (by positivity)]
  have hlog_invN : Real.log ((1 - p1) / (1 - p0)) = -N := by
    change Real.log ((1 - p1) / (1 - p0)) = -Real.log ((1 - p0) / (1 - p1))
    have hEq : ((1 - p1) / (1 - p0) : ℝ) = (((1 - p0) / (1 - p1) : ℝ))⁻¹ := by
      field_simp [h1mp0.ne', h1mp1.ne']
    rw [hEq, Real.log_inv]
  have hx0 : 0 < p1 / p0 := by positivity
  have hy0 : 0 < (1 - p1) / (1 - p0) := by positivity
  have hx_ne_y : p1 / p0 ≠ (1 - p1) / (1 - p0) := by
    have hx_gt1 : 1 < p1 / p0 := (one_lt_div hp0).2 hp0p1
    have hy_lt1 : (1 - p1) / (1 - p0) < 1 := (div_lt_one h1mp0).2 (by linarith)
    intro hEq
    rw [hEq] at hx_gt1
    linarith
  have havg0 : p0 * (p1 / p0) + (1 - p0) * ((1 - p1) / (1 - p0)) = 1 := by
    field_simp [hp0.ne', h1mp0.ne']
    ring
  have hbound0_raw :
      p0 * Real.log (p1 / p0) + (1 - p0) * Real.log ((1 - p1) / (1 - p0)) < 0 := by
    exact weighted_log_lt_zero p0 (p1 / p0) ((1 - p1) / (1 - p0))
      hp0 (by linarith) hx0 hy0 hx_ne_y havg0
  have hη_gt_p0 : p0 < η := by
    have hbound0 : p0 * Real.log (p1 / p0) - (1 - p0) * N < 0 := by
      simpa [hlog_invN] using hbound0_raw
    have htmp' : p0 * D - N < 0 := by
      calc
        p0 * D - N = p0 * (Real.log (p1 / p0) + N) - N := by rw [hD_split]
        _ = p0 * Real.log (p1 / p0) - (1 - p0) * N := by ring
        _ < 0 := hbound0
    have htmp : p0 * D < N := by
      linarith
    rw [hη_def]
    exact (lt_div_iff₀ hD_pos).2 htmp
  have hx1 : 0 < p0 / p1 := by positivity
  have hy1 : 0 < (1 - p0) / (1 - p1) := by positivity
  have hx1_ne_y1 : p0 / p1 ≠ (1 - p0) / (1 - p1) := by
    have hx_lt1 : p0 / p1 < 1 := (div_lt_one hp1).2 hp0p1
    have hy_gt1 : 1 < (1 - p0) / (1 - p1) := (one_lt_div h1mp1).2 (by linarith)
    intro hEq
    rw [hEq] at hx_lt1
    linarith
  have havg1 : p1 * (p0 / p1) + (1 - p1) * ((1 - p0) / (1 - p1)) = 1 := by
    field_simp [hp1.ne', h1mp1.ne']
    ring
  have hbound1_raw :
      p1 * Real.log (p0 / p1) + (1 - p1) * Real.log ((1 - p0) / (1 - p1)) < 0 := by
    exact weighted_log_lt_zero p1 (p0 / p1) ((1 - p0) / (1 - p1))
      hp1 hp1lt1 hx1 hy1 hx1_ne_y1 havg1
  have hη_lt_p1 : η < p1 := by
    have hlogp : Real.log (p0 / p1) = -Real.log (p1 / p0) := by
      have hEq : (p0 / p1 : ℝ) = ((p1 / p0 : ℝ))⁻¹ := by
        field_simp [hp0.ne', hp1.ne']
      rw [hEq, Real.log_inv]
    have htmp' : N - p1 * D < 0 := by
      have hbound1 : -p1 * Real.log (p1 / p0) + (1 - p1) * N < 0 := by
        simpa [hlogp] using hbound1_raw
      calc
        N - p1 * D = N - p1 * (Real.log (p1 / p0) + N) := by rw [hD_split]
        _ = -p1 * Real.log (p1 / p0) + (1 - p1) * N := by ring
        _ < 0 := hbound1
    have htmp : N < p1 * D := by
      linarith
    rw [hη_def]
    exact (div_lt_iff₀ hD_pos).2 htmp
  have hη_mul : η * D = N := by
    calc
      η * D = (N / D) * D := by rw [hη_def]
      _ = N := by field_simp [hD_ne]
  have hlog_one_sub : N = Real.log (1 - p0) - Real.log (1 - p1) := by
    change Real.log ((1 - p0) / (1 - p1)) = Real.log (1 - p0) - Real.log (1 - p1)
    rw [Real.log_div h1mp0.ne' h1mp1.ne']
  have hlinear :
      η * (Real.log p1 - Real.log p0) = (1 - η) * (Real.log (1 - p0) - Real.log (1 - p1)) := by
    have hlogpp : Real.log (p1 / p0) = Real.log p1 - Real.log p0 := by
      rw [Real.log_div hp1.ne' hp0.ne']
    have hη_mul' :
        η * ((Real.log p1 - Real.log p0) + (Real.log (1 - p0) - Real.log (1 - p1))) =
          Real.log (1 - p0) - Real.log (1 - p1) := by
      calc
        η * ((Real.log p1 - Real.log p0) + (Real.log (1 - p0) - Real.log (1 - p1))) = η * D := by
          rw [hD_split, hlogpp, hlog_one_sub]
        _ = N := hη_mul
        _ = Real.log (1 - p0) - Real.log (1 - p1) := hlog_one_sub
    linarith
  have hη_pos : 0 < η := lt_trans hp0 hη_gt_p0
  have h1mη_pos : 0 < 1 - η := by linarith
  refine ⟨hη_gt_p0, hη_lt_p1, ?_⟩
  rw [Real.log_div hη_pos.ne' hp0.ne', Real.log_div h1mη_pos.ne' h1mp0.ne',
    Real.log_div hη_pos.ne' hp1.ne', Real.log_div h1mη_pos.ne' h1mp1.ne']
  ring_nf
  linarith

end Omega.Folding
