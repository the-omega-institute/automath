import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete two-atom entropy-regularized variational package: the Jensen functional
`∑ qᵢ log (wᵢ / qᵢ)` is bounded above by `log (w₀ + w₁)`, the canonical normalized choice
attains the bound, and equality forces the optimizer to be the normalized weight vector. -/
def xi_jensen_entropy_regularized_variational_statement : Prop :=
  ∀ {w0 w1 q0 q1 : ℝ},
    0 < w0 →
    0 < w1 →
    0 < q0 →
    0 < q1 →
    q0 + q1 = 1 →
      let s := w0 + w1
      let p0 := w0 / s
      let p1 := w1 / s
      q0 * Real.log (w0 / q0) + q1 * Real.log (w1 / q1) ≤ Real.log s ∧
        p0 * Real.log (w0 / p0) + p1 * Real.log (w1 / p1) = Real.log s ∧
        (q0 * Real.log (w0 / q0) + q1 * Real.log (w1 / q1) = Real.log s →
          q0 = p0 ∧ q1 = p1)

/-- Paper label: `thm:xi-jensen-entropy-regularized-variational`. -/
theorem paper_xi_jensen_entropy_regularized_variational :
    xi_jensen_entropy_regularized_variational_statement := by
  intro w0 w1 q0 q1 hw0 hw1 hq0 hq1 hsum
  set s : ℝ := w0 + w1
  set p0 : ℝ := w0 / s
  set p1 : ℝ := w1 / s
  have hs : 0 < s := by
    dsimp [s]
    linarith
  have hq0_ne : q0 ≠ 0 := hq0.ne'
  have hq1_ne : q1 ≠ 0 := hq1.ne'
  have hs_ne : s ≠ 0 := hs.ne'
  have hp_sum : p0 + p1 = 1 := by
    dsimp [p0, p1, s]
    field_simp [hs_ne]
  have hupper :
      q0 * Real.log (w0 / q0) + q1 * Real.log (w1 / q1) ≤ Real.log s := by
    let x0 : ℝ := w0 / q0
    let x1 : ℝ := w1 / q1
    have hx0 : 0 < x0 := by
      dsimp [x0]
      exact div_pos hw0 hq0
    have hx1 : 0 < x1 := by
      dsimp [x1]
      exact div_pos hw1 hq1
    by_cases hxx : x0 = x1
    · have hsumx : s = q0 * x0 + q1 * x1 := by
        dsimp [s, x0, x1]
        field_simp [hq0_ne, hq1_ne]
      have hs_eq : s = x0 := by
        calc
          s = q0 * x0 + q1 * x1 := hsumx
          _ = (q0 + q1) * x0 := by rw [hxx]; ring
          _ = x0 := by rw [hsum]; ring
      calc
        q0 * Real.log (w0 / q0) + q1 * Real.log (w1 / q1)
            = q0 * Real.log x0 + q1 * Real.log x1 := by rfl
        _ = (q0 + q1) * Real.log x0 := by rw [hxx]; ring
        _ = Real.log x0 := by rw [hsum]; ring
        _ = Real.log s := by rw [hs_eq]
        _ ≤ Real.log s := le_rfl
    · have hstrict :
        q0 * Real.log x0 + q1 * Real.log x1 < Real.log (q0 * x0 + q1 * x1) := by
          exact strictConcaveOn_log_Ioi.2 hx0 hx1 hxx hq0 hq1 hsum
      have hsumx : q0 * x0 + q1 * x1 = s := by
        dsimp [s, x0, x1]
        field_simp [hq0_ne, hq1_ne]
      have : q0 * Real.log (w0 / q0) + q1 * Real.log (w1 / q1) < Real.log s := by
        simpa [x0, x1, hsumx] using hstrict
      exact this.le
  have hcanon :
      p0 * Real.log (w0 / p0) + p1 * Real.log (w1 / p1) = Real.log s := by
    have hw0_over : w0 / p0 = s := by
      dsimp [p0]
      field_simp [hs_ne]
    have hw1_over : w1 / p1 = s := by
      dsimp [p1]
      field_simp [hs_ne]
    calc
      p0 * Real.log (w0 / p0) + p1 * Real.log (w1 / p1)
          = p0 * Real.log s + p1 * Real.log s := by rw [hw0_over, hw1_over]
      _ = (p0 + p1) * Real.log s := by ring
      _ = Real.log s := by rw [hp_sum]; ring
  refine ⟨hupper, hcanon, ?_⟩
  intro heq
  let x0 : ℝ := w0 / q0
  let x1 : ℝ := w1 / q1
  have hx0 : 0 < x0 := by
    dsimp [x0]
    exact div_pos hw0 hq0
  have hx1 : 0 < x1 := by
    dsimp [x1]
    exact div_pos hw1 hq1
  have hxx : x0 = x1 := by
    by_contra hneq
    have hstrict :
        q0 * Real.log x0 + q1 * Real.log x1 < Real.log (q0 * x0 + q1 * x1) := by
      exact strictConcaveOn_log_Ioi.2 hx0 hx1 hneq hq0 hq1 hsum
    have hsumx : q0 * x0 + q1 * x1 = s := by
      dsimp [s, x0, x1]
      field_simp [hq0_ne, hq1_ne]
    have : q0 * Real.log (w0 / q0) + q1 * Real.log (w1 / q1) < Real.log s := by
      simpa [x0, x1, hsumx] using hstrict
    linarith
  have hcross : w0 * q1 = w1 * q0 := by
    dsimp [x0, x1] at hxx
    have := congrArg (fun t : ℝ => t * (q0 * q1)) hxx
    field_simp [hq0_ne, hq1_ne] at this
    linarith
  have hsq0 : s * q0 = w0 := by
    calc
      s * q0 = (w0 + w1) * q0 := by rfl
      _ = w0 * q0 + w1 * q0 := by ring
      _ = w0 * q0 + w0 * q1 := by rw [hcross]
      _ = w0 * (q0 + q1) := by ring
      _ = w0 := by rw [hsum]; ring
  have hsq1 : s * q1 = w1 := by
    calc
      s * q1 = (w0 + w1) * q1 := by rfl
      _ = w0 * q1 + w1 * q1 := by ring
      _ = w1 * q0 + w1 * q1 := by rw [hcross]
      _ = w1 * (q0 + q1) := by ring
      _ = w1 := by rw [hsum]; ring
  have hq0_eq : q0 = p0 := by
    dsimp [p0]
    exact (eq_div_iff hs_ne).2 (by simpa [mul_comm] using hsq0)
  have hq1_eq : q1 = p1 := by
    dsimp [p1]
    exact (eq_div_iff hs_ne).2 (by simpa [mul_comm] using hsq1)
  exact ⟨hq0_eq, hq1_eq⟩

end Omega.Zeta
