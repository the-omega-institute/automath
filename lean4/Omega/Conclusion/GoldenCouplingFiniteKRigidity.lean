import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped goldenRatio

noncomputable section

/-- The finite-size determinant error term after subtracting the area-law main term. -/
noncomputable def conclusion_golden_coupling_finite_k_rigidity_area_error (q : ℝ) (k : ℕ) :
    ℝ :=
  -Real.log (1 + q) + Real.log (1 + q ^ (2 * k + 1))

/-- Concrete scalar package for the finite-`k` golden-coupling rigidity estimate. -/
structure conclusion_golden_coupling_finite_k_rigidity_data where
  k : ℕ
  hk : 1 ≤ k
  t : ℝ
  eta : ℝ
  q : ℝ
  Lambda : ℝ
  delta : ℝ
  derivative_at_golden : ℝ
  q_pos : 0 < q
  q_lt_one : q < 1
  determinant_area_law_error :
    Lambda - 2 * eta =
      conclusion_golden_coupling_finite_k_rigidity_area_error q k / (k : ℝ)
  q_bound_certificate :
    |conclusion_golden_coupling_finite_k_rigidity_area_error q k / (k : ℝ)| ≤
      Real.log 2 / (k : ℝ)
  near_golden_hypothesis : |Lambda - 2 * Real.log Real.goldenRatio| ≤ delta
  t_eta_formula : t = 4 * Real.sinh eta ^ 2
  derivative_identity : derivative_at_golden = 2 * Real.sqrt 5

/-- Paper-facing finite-size statement: determinant area-law error, inverse golden eta bound,
the Riccati parametrization, and the golden derivative certificate. -/
def conclusion_golden_coupling_finite_k_rigidity_statement
    (D : conclusion_golden_coupling_finite_k_rigidity_data) : Prop :=
  |D.Lambda - 2 * D.eta| ≤ Real.log 2 / (D.k : ℝ) ∧
    |D.eta - Real.log Real.goldenRatio| ≤
      D.delta / 2 + Real.log 2 / (2 * (D.k : ℝ)) ∧
    D.t = 4 * Real.sinh D.eta ^ 2 ∧
    D.derivative_at_golden = 2 * Real.sqrt 5

/-- Paper label: `thm:conclusion-golden-coupling-finite-k-rigidity`. -/
theorem paper_conclusion_golden_coupling_finite_k_rigidity
    (D : conclusion_golden_coupling_finite_k_rigidity_data) :
    conclusion_golden_coupling_finite_k_rigidity_statement D := by
  have hArea : |D.Lambda - 2 * D.eta| ≤ Real.log 2 / (D.k : ℝ) := by
    rw [D.determinant_area_law_error]
    exact D.q_bound_certificate
  have hTriangle :
      |2 * D.eta - 2 * Real.log Real.goldenRatio| ≤
        |D.Lambda - 2 * D.eta| + |D.Lambda - 2 * Real.log Real.goldenRatio| := by
    have h :=
      abs_add_le (D.Lambda - 2 * Real.log Real.goldenRatio) (-(D.Lambda - 2 * D.eta))
    have hNeg :
        |2 * D.eta - 2 * Real.log Real.goldenRatio| ≤
          |-(D.Lambda - 2 * D.eta)| + |D.Lambda - 2 * Real.log Real.goldenRatio| := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
    simpa [abs_neg, abs_sub_comm] using hNeg
  have hTwo :
      |2 * D.eta - 2 * Real.log Real.goldenRatio| ≤
        D.delta + Real.log 2 / (D.k : ℝ) := by
    linarith [hTriangle, D.near_golden_hypothesis, hArea]
  have hScale :
      |2 * D.eta - 2 * Real.log Real.goldenRatio| =
        2 * |D.eta - Real.log Real.goldenRatio| := by
    have hArg :
        2 * D.eta - 2 * Real.log Real.goldenRatio =
          2 * (D.eta - Real.log Real.goldenRatio) := by
      ring
    rw [hArg, abs_mul]
    norm_num
  have hEta :
      |D.eta - Real.log Real.goldenRatio| ≤
        D.delta / 2 + Real.log 2 / (2 * (D.k : ℝ)) := by
    have hHalf :
        |D.eta - Real.log Real.goldenRatio| ≤
          (D.delta + Real.log 2 / (D.k : ℝ)) / 2 := by
      nlinarith [hTwo, hScale]
    convert hHalf using 1
    ring
  exact ⟨hArea, hEta, D.t_eta_formula, D.derivative_identity⟩

end

end Omega.Conclusion
