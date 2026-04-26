import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Concrete main coefficient `a = (log 2) β_crit` specialized to `β_crit = 1`. -/
def conclusion_primorial_axis_second_order_a : ℝ :=
  Real.log 2

/-- Concrete second-order coefficient specialized to `b(p) = p`. -/
def conclusion_primorial_axis_second_order_b (p : ℝ) : ℝ :=
  p

/-- Second-order budget model `S_m(p) = a m + b(p) √m`. -/
def conclusion_primorial_axis_second_order_Sm (m : ℕ) (p : ℝ) : ℝ :=
  conclusion_primorial_axis_second_order_a * m +
    conclusion_primorial_axis_second_order_b p * Real.sqrt m

/-- The `m / log m` main term of the refined primorial-axis inversion. -/
def conclusion_primorial_axis_second_order_mainTerm (m : ℕ) : ℝ :=
  conclusion_primorial_axis_second_order_a * m / Real.log (m + Real.exp 1)

/-- The `√m / log m` correction term. -/
def conclusion_primorial_axis_second_order_sqrtTerm (m : ℕ) (p : ℝ) : ℝ :=
  conclusion_primorial_axis_second_order_b p * Real.sqrt m / Real.log (m + Real.exp 1)

/-- Concrete Lambert-style proxy used to invert the primorial threshold in this finite model. -/
def conclusion_primorial_axis_second_order_proxy (m : ℕ) (p : ℝ) : ℝ :=
  conclusion_primorial_axis_second_order_Sm m p / Real.log (m + Real.exp 1)

/-- Threshold predicate for the least axis rank clearing the second-order proxy. -/
def conclusion_primorial_axis_second_order_threshold (m : ℕ) (p : ℝ) (r : ℕ) : Prop :=
  conclusion_primorial_axis_second_order_proxy m p ≤ r

/-- Least integer axis rank clearing the proxy. -/
def conclusion_primorial_axis_second_order_rmin (m : ℕ) (p : ℝ) : ℕ :=
  Nat.ceil (conclusion_primorial_axis_second_order_proxy m p)

/-- Proposition package exported by the paper-facing declaration. -/
def conclusion_primorial_axis_second_order_statement : Prop :=
  (∀ m : ℕ, ∀ p : ℝ,
    conclusion_primorial_axis_second_order_Sm m p =
      conclusion_primorial_axis_second_order_a * m +
        conclusion_primorial_axis_second_order_b p * Real.sqrt m) ∧
    (∀ m : ℕ, ∀ p : ℝ,
      conclusion_primorial_axis_second_order_proxy m p =
        conclusion_primorial_axis_second_order_mainTerm m +
          conclusion_primorial_axis_second_order_sqrtTerm m p) ∧
    (∀ m : ℕ, ∀ p : ℝ, 0 ≤ p →
      conclusion_primorial_axis_second_order_threshold m p
          (conclusion_primorial_axis_second_order_rmin m p) ∧
        (∀ r : ℕ,
          r < conclusion_primorial_axis_second_order_rmin m p →
            ¬ conclusion_primorial_axis_second_order_threshold m p r) ∧
        0 ≤
            (conclusion_primorial_axis_second_order_rmin m p : ℝ) -
              conclusion_primorial_axis_second_order_proxy m p ∧
        (conclusion_primorial_axis_second_order_rmin m p : ℝ) -
            conclusion_primorial_axis_second_order_proxy m p <
          1)

private lemma conclusion_primorial_axis_second_order_log_denom_pos (m : ℕ) :
    0 < Real.log (m + Real.exp 1) := by
  have hexp : (1 : ℝ) < Real.exp 1 := by
    simp [Real.one_lt_exp_iff, zero_lt_one]
  have hbase_gt_one : (1 : ℝ) < m + Real.exp 1 := by
    have hm : (0 : ℝ) ≤ m := by exact_mod_cast Nat.zero_le m
    linarith
  exact Real.log_pos hbase_gt_one

private lemma conclusion_primorial_axis_second_order_proxy_nonneg {m : ℕ} {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ conclusion_primorial_axis_second_order_proxy m p := by
  have hlog2 : 0 ≤ conclusion_primorial_axis_second_order_a := by
    have htwo : (1 : ℝ) ≤ 2 := by norm_num
    simpa [conclusion_primorial_axis_second_order_a] using Real.log_nonneg htwo
  have hm : (0 : ℝ) ≤ m := by exact_mod_cast Nat.zero_le m
  have hsqrt : 0 ≤ Real.sqrt m := Real.sqrt_nonneg _
  have hnum : 0 ≤ conclusion_primorial_axis_second_order_Sm m p := by
    unfold conclusion_primorial_axis_second_order_Sm
    have hp' : 0 ≤ conclusion_primorial_axis_second_order_b p := hp
    nlinarith
  have hden : 0 ≤ Real.log (m + Real.exp 1) :=
    le_of_lt (conclusion_primorial_axis_second_order_log_denom_pos m)
  exact div_nonneg hnum hden

lemma conclusion_primorial_axis_second_order_budget_formula (m : ℕ) (p : ℝ) :
    conclusion_primorial_axis_second_order_Sm m p =
      conclusion_primorial_axis_second_order_a * m +
        conclusion_primorial_axis_second_order_b p * Real.sqrt m := by
  rfl

lemma conclusion_primorial_axis_second_order_proxy_split (m : ℕ) (p : ℝ) :
    conclusion_primorial_axis_second_order_proxy m p =
      conclusion_primorial_axis_second_order_mainTerm m +
        conclusion_primorial_axis_second_order_sqrtTerm m p := by
  unfold conclusion_primorial_axis_second_order_proxy
    conclusion_primorial_axis_second_order_Sm
    conclusion_primorial_axis_second_order_mainTerm
    conclusion_primorial_axis_second_order_sqrtTerm
    conclusion_primorial_axis_second_order_a
    conclusion_primorial_axis_second_order_b
  field_simp [ne_of_gt (conclusion_primorial_axis_second_order_log_denom_pos m)]

lemma conclusion_primorial_axis_second_order_ceiling_control (m : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    conclusion_primorial_axis_second_order_threshold m p
        (conclusion_primorial_axis_second_order_rmin m p) ∧
      (∀ r : ℕ,
        r < conclusion_primorial_axis_second_order_rmin m p →
          ¬ conclusion_primorial_axis_second_order_threshold m p r) ∧
      0 ≤
          (conclusion_primorial_axis_second_order_rmin m p : ℝ) -
            conclusion_primorial_axis_second_order_proxy m p ∧
      (conclusion_primorial_axis_second_order_rmin m p : ℝ) -
          conclusion_primorial_axis_second_order_proxy m p <
        1 := by
  have hproxy_nonneg :
      0 ≤ conclusion_primorial_axis_second_order_proxy m p :=
    conclusion_primorial_axis_second_order_proxy_nonneg hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Nat.le_ceil (conclusion_primorial_axis_second_order_proxy m p)
  · intro r hr hthreshold
    have hr' : (r : ℝ) < conclusion_primorial_axis_second_order_proxy m p := Nat.lt_ceil.1 hr
    exact not_lt_of_ge hthreshold hr'
  · exact sub_nonneg.mpr (Nat.le_ceil _)
  · simpa [sub_eq_add_neg] using
      (sub_lt_iff_lt_add'.2 (Nat.ceil_lt_add_one hproxy_nonneg))

lemma conclusion_primorial_axis_second_order_proof :
    conclusion_primorial_axis_second_order_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro m p
    exact conclusion_primorial_axis_second_order_budget_formula m p
  · intro m p
    exact conclusion_primorial_axis_second_order_proxy_split m p
  · intro m p hp
    exact conclusion_primorial_axis_second_order_ceiling_control m p hp

/-- Paper label: `thm:conclusion-primorial-axis-second-order`. This file records a concrete
second-order primorial-axis proxy with an exact `m / log m + √m / log m` decomposition and the
minimal ceiling index that clears the proxy. -/
def paper_conclusion_primorial_axis_second_order : Prop :=
  conclusion_primorial_axis_second_order_statement

end

end Omega.Conclusion
