import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-collision-perron-logconvex-renyi-concavity`. -/
theorem paper_conclusion_collision_perron_logconvex_renyi_concavity
    (r P h : ℕ → ℝ)
    (hrpos : ∀ q, 1 ≤ q → 0 < r q)
    (hlogconvex : ∀ q, 1 ≤ q → r (q + 1) ^ (2 : ℕ) ≤ r q * r (q + 2))
    (hP : ∀ q, 1 ≤ q → P q = Real.log (r q))
    (hh : ∀ q, 1 ≤ q → h q = (q : ℝ) * Real.log 2 - P q) :
    ∀ q, 1 ≤ q →
      r (q + 1) ^ (2 : ℕ) ≤ r q * r (q + 2) ∧
        P (q + 1) - P q ≤ P (q + 2) - P (q + 1) ∧
          h (q + 2) - 2 * h (q + 1) + h q ≤ 0 := by
  intro q hq
  have hq1 : 1 ≤ q + 1 := by omega
  have hq2 : 1 ≤ q + 2 := by omega
  have hrq : 0 < r q := hrpos q hq
  have hrq1 : 0 < r (q + 1) := hrpos (q + 1) hq1
  have hrq2 : 0 < r (q + 2) := hrpos (q + 2) hq2
  have hfirst : r (q + 1) ^ (2 : ℕ) ≤ r q * r (q + 2) := hlogconvex q hq
  have hlog_le :
      Real.log (r (q + 1) ^ (2 : ℕ)) ≤ Real.log (r q * r (q + 2)) := by
    exact Real.log_le_log (sq_pos_of_ne_zero hrq1.ne') hfirst
  have hlog_sq :
      Real.log (r (q + 1) ^ (2 : ℕ)) = 2 * Real.log (r (q + 1)) := by
    rw [Real.log_pow]
    norm_num
  have hlog_mul :
      Real.log (r q * r (q + 2)) = Real.log (r q) + Real.log (r (q + 2)) := by
    rw [Real.log_mul hrq.ne' hrq2.ne']
  have hP_second :
      P (q + 1) - P q ≤ P (q + 2) - P (q + 1) := by
    rw [hlog_sq, hlog_mul] at hlog_le
    rw [hP q hq, hP (q + 1) hq1, hP (q + 2) hq2]
    linarith
  have hhq : h q = (q : ℝ) * Real.log 2 - P q := hh q hq
  have hhq1 : h (q + 1) = ((q + 1 : ℕ) : ℝ) * Real.log 2 - P (q + 1) :=
    hh (q + 1) hq1
  have hhq2 : h (q + 2) = ((q + 2 : ℕ) : ℝ) * Real.log 2 - P (q + 2) :=
    hh (q + 2) hq2
  have hthird : h (q + 2) - 2 * h (q + 1) + h q ≤ 0 := by
    rw [hhq, hhq1, hhq2]
    norm_num
    linarith
  exact ⟨hfirst, hP_second, hthird⟩

end Omega.Conclusion
