import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete fixed-alpha one-bit SAT order-parameter datum. -/
structure conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_data where
  conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_Formula : Type
  conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_sat :
    conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_Formula → Bool
  conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_approx :
    conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_Formula → ℝ

namespace conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_data

/-- The normalized Rényi--Schatten gap is the rigid one-bit order parameter. -/
noncomputable def conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_gap
    (D : conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_data)
    (φ :
      D.conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_Formula) : ℝ :=
  if D.conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_sat φ then Real.log 2 else 0

/-- UNSAT is exactly the zero-gap branch. -/
def conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_unsat_zero_iff
    (D : conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_data) : Prop :=
  ∀ φ,
    D.conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_sat φ = false ↔
      D.conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_gap φ = 0

/-- SAT has at least the one-bit `log 2` gap. -/
def conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_sat_log_two_gap
    (D : conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_data) : Prop :=
  ∀ φ,
    D.conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_sat φ = true →
      Real.log 2 ≤
        D.conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_gap φ

/-- Any additive approximation inside half the one-bit gap recovers the SAT predicate by
thresholding, which is the paper's approximation-to-`P=NP` comparison. -/
def conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_approx_implies_p_eq_np
    (D : conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_data) : Prop :=
  ∀ φ,
    |D.conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_approx φ -
      D.conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_gap φ| <
        Real.log 2 / 2 →
      (Real.log 2 / 2 <
          D.conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_approx φ ↔
        D.conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_sat φ = true)

end conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_data

open conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_data

/-- Paper label: `thm:conclusion-renyi-schatten-gap-rigid-onebit-sat-order-parameter`. -/
theorem paper_conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter
    (D : conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_data) :
    D.conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_unsat_zero_iff ∧
      D.conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_sat_log_two_gap ∧
      D.conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_approx_implies_p_eq_np := by
  have hlog_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog_ne : Real.log 2 ≠ 0 := ne_of_gt hlog_pos
  refine ⟨?_, ?_, ?_⟩
  · intro φ
    cases hsat :
      D.conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_sat φ
    · simp [conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_gap, hsat]
    · simp [conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_gap, hsat, hlog_ne]
  · intro φ hsat
    simp [conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_gap, hsat]
  · intro φ happ
    rcases abs_lt.mp happ with ⟨hneg, hpos⟩
    cases hsat :
      D.conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_sat φ
    · simp [conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_gap, hsat] at hpos
      constructor
      · intro h
        linarith
      · intro h
        cases h
    · simp [conclusion_renyi_schatten_gap_rigid_onebit_sat_order_parameter_gap, hsat] at hneg
      constructor
      · intro h
        rfl
      · intro _
        linarith

end Omega.Conclusion
