import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- The monotone logarithmic proxy governing the primorial axis threshold. The additive `exp 1`
shifts keep both logarithms positive on the whole half-line `P ≥ 0`. -/
def conclusion_primorial_axis_dimension_law_scale (P : ℝ) : ℝ :=
  Real.log (P + Real.exp 1) / Real.log (Real.log (P + Real.exp 1) + Real.exp 1)

/-- The least axis dimension meeting the primorial threshold proxy. -/
def conclusion_primorial_axis_dimension_law_k_min (P : ℝ) : ℕ :=
  Nat.ceil (conclusion_primorial_axis_dimension_law_scale P)

/-- Threshold predicate used to define the minimal admissible axis dimension. -/
def conclusion_primorial_axis_dimension_law_threshold (P : ℝ) (k : ℕ) : Prop :=
  conclusion_primorial_axis_dimension_law_scale P ≤ k

  private lemma conclusion_primorial_axis_dimension_law_scale_nonneg {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ conclusion_primorial_axis_dimension_law_scale P := by
  have hexp_one_gt_one : 1 < Real.exp 1 := by
    simp [Real.one_lt_exp_iff] 
  have hbase_ge_one : 1 ≤ P + Real.exp 1 := by
    linarith
  have hnum_nonneg : 0 ≤ Real.log (P + Real.exp 1) := by
    exact Real.log_nonneg hbase_ge_one
  have hlog_ge_one : 1 ≤ Real.log (P + Real.exp 1) + Real.exp 1 := by
    linarith [hnum_nonneg, le_of_lt hexp_one_gt_one]
  have hden_nonneg : 0 ≤ Real.log (Real.log (P + Real.exp 1) + Real.exp 1) := by
    exact Real.log_nonneg hlog_ge_one
  exact div_nonneg hnum_nonneg hden_nonneg

/-- Paper label: `prop:conclusion-primorial-axis-dimension-law`. The least threshold index
`k_min` is the ceiling of the logarithmic primorial proxy, hence it is the minimal index above the
proxy and differs from that proxy by less than one. -/
theorem paper_conclusion_primorial_axis_dimension_law (P : ℝ) (hP : 0 ≤ P) :
    conclusion_primorial_axis_dimension_law_threshold P
        (conclusion_primorial_axis_dimension_law_k_min P) ∧
      (∀ k : ℕ,
        k < conclusion_primorial_axis_dimension_law_k_min P →
          ¬ conclusion_primorial_axis_dimension_law_threshold P k) ∧
      0 ≤
          (conclusion_primorial_axis_dimension_law_k_min P : ℝ) -
            conclusion_primorial_axis_dimension_law_scale P ∧
      (conclusion_primorial_axis_dimension_law_k_min P : ℝ) -
          conclusion_primorial_axis_dimension_law_scale P <
        1 := by
  have hscale_nonneg :
      0 ≤ conclusion_primorial_axis_dimension_law_scale P :=
    conclusion_primorial_axis_dimension_law_scale_nonneg hP
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Nat.le_ceil (conclusion_primorial_axis_dimension_law_scale P)
  · intro k hk hthreshold
    have hk' : (k : ℝ) < conclusion_primorial_axis_dimension_law_scale P :=
      Nat.lt_ceil.1 hk
    exact not_lt_of_ge hthreshold hk'
  · exact sub_nonneg.mpr (Nat.le_ceil _)
  · simpa [sub_eq_add_neg] using
      (sub_lt_iff_lt_add'.2 (Nat.ceil_lt_add_one hscale_nonneg))

end

end Omega.Conclusion
