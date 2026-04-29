import Mathlib.Tactic
import Omega.Conclusion.Window6Collision

namespace Omega.Conclusion

/-- Audited multiplicity histogram for the window-`6` degree spectrum. -/
def conclusion_window6_degree_spectrum_capacity_tail_identity_histogram (d : ℕ) : ℕ :=
  Omega.cBinFiberHist 6 d

/-- Continuous capacity curve attached to the audited histogram `{2:8,3:4,4:9}`. -/
noncomputable def conclusion_window6_degree_spectrum_capacity_tail_identity_capacity_curve
    (T : ℝ) : ℝ :=
  (conclusion_window6_degree_spectrum_capacity_tail_identity_histogram 2 : ℝ) *
      min (2 : ℝ) T +
    (conclusion_window6_degree_spectrum_capacity_tail_identity_histogram 3 : ℝ) *
      min (3 : ℝ) T +
    (conclusion_window6_degree_spectrum_capacity_tail_identity_histogram 4 : ℝ) *
      min (4 : ℝ) T

/-- Tail count `N₆(q) = #{w : d(w) ≥ q}` for the audited histogram. -/
def conclusion_window6_degree_spectrum_capacity_tail_identity_tail_count (q : ℕ) : ℕ :=
  (if q ≤ 2 then conclusion_window6_degree_spectrum_capacity_tail_identity_histogram 2 else 0) +
    (if q ≤ 3 then conclusion_window6_degree_spectrum_capacity_tail_identity_histogram 3 else 0) +
    (if q ≤ 4 then conclusion_window6_degree_spectrum_capacity_tail_identity_histogram 4 else 0)

/-- Right-derivative values of the continuous capacity curve at the integer breakpoints. -/
def conclusion_window6_degree_spectrum_capacity_tail_identity_right_derivative (T : ℕ) : ℕ :=
  conclusion_window6_degree_spectrum_capacity_tail_identity_tail_count (T + 1)

/-- The audited window-`6` tail counts and right-derivative values coincide, producing the degree
spectrum constants `(21,13,9)`. -/
def conclusion_window6_degree_spectrum_capacity_tail_identity_statement : Prop :=
  conclusion_window6_degree_spectrum_capacity_tail_identity_histogram 2 = 8 ∧
    conclusion_window6_degree_spectrum_capacity_tail_identity_histogram 3 = 4 ∧
    conclusion_window6_degree_spectrum_capacity_tail_identity_histogram 4 = 9 ∧
    conclusion_window6_degree_spectrum_capacity_tail_identity_capacity_curve 1 = 21 ∧
    conclusion_window6_degree_spectrum_capacity_tail_identity_capacity_curve 2 = 42 ∧
    conclusion_window6_degree_spectrum_capacity_tail_identity_capacity_curve 3 = 55 ∧
    conclusion_window6_degree_spectrum_capacity_tail_identity_tail_count 2 = 21 ∧
    conclusion_window6_degree_spectrum_capacity_tail_identity_tail_count 3 = 13 ∧
    conclusion_window6_degree_spectrum_capacity_tail_identity_tail_count 4 = 9 ∧
    conclusion_window6_degree_spectrum_capacity_tail_identity_right_derivative 1 = 21 ∧
    conclusion_window6_degree_spectrum_capacity_tail_identity_right_derivative 2 = 13 ∧
    conclusion_window6_degree_spectrum_capacity_tail_identity_right_derivative 3 = 9 ∧
    conclusion_window6_degree_spectrum_capacity_tail_identity_right_derivative 1 =
      conclusion_window6_degree_spectrum_capacity_tail_identity_tail_count 2 ∧
    conclusion_window6_degree_spectrum_capacity_tail_identity_right_derivative 2 =
      conclusion_window6_degree_spectrum_capacity_tail_identity_tail_count 3 ∧
    conclusion_window6_degree_spectrum_capacity_tail_identity_right_derivative 3 =
      conclusion_window6_degree_spectrum_capacity_tail_identity_tail_count 4 ∧
    (conclusion_window6_degree_spectrum_capacity_tail_identity_right_derivative 1,
      conclusion_window6_degree_spectrum_capacity_tail_identity_right_derivative 2,
      conclusion_window6_degree_spectrum_capacity_tail_identity_right_derivative 3) =
        (21, 13, 9)

/-- Paper label: `thm:conclusion-window6-degree-spectrum-capacity-tail-identity`. -/
theorem paper_conclusion_window6_degree_spectrum_capacity_tail_identity :
    conclusion_window6_degree_spectrum_capacity_tail_identity_statement := by
  refine ⟨Omega.cBinFiberHist_6_2, Omega.cBinFiberHist_6_3, Omega.cBinFiberHist_6_4, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · norm_num [conclusion_window6_degree_spectrum_capacity_tail_identity_capacity_curve,
      conclusion_window6_degree_spectrum_capacity_tail_identity_histogram,
      Omega.cBinFiberHist_6_2, Omega.cBinFiberHist_6_3, Omega.cBinFiberHist_6_4]
  · norm_num [conclusion_window6_degree_spectrum_capacity_tail_identity_capacity_curve,
      conclusion_window6_degree_spectrum_capacity_tail_identity_histogram,
      Omega.cBinFiberHist_6_2, Omega.cBinFiberHist_6_3, Omega.cBinFiberHist_6_4]
  · norm_num [conclusion_window6_degree_spectrum_capacity_tail_identity_capacity_curve,
      conclusion_window6_degree_spectrum_capacity_tail_identity_histogram,
      Omega.cBinFiberHist_6_2, Omega.cBinFiberHist_6_3, Omega.cBinFiberHist_6_4]
  · norm_num [conclusion_window6_degree_spectrum_capacity_tail_identity_tail_count,
      conclusion_window6_degree_spectrum_capacity_tail_identity_histogram,
      Omega.cBinFiberHist_6_2, Omega.cBinFiberHist_6_3, Omega.cBinFiberHist_6_4]
  · norm_num [conclusion_window6_degree_spectrum_capacity_tail_identity_tail_count,
      conclusion_window6_degree_spectrum_capacity_tail_identity_histogram,
      Omega.cBinFiberHist_6_2, Omega.cBinFiberHist_6_3, Omega.cBinFiberHist_6_4]
  · norm_num [conclusion_window6_degree_spectrum_capacity_tail_identity_tail_count,
      conclusion_window6_degree_spectrum_capacity_tail_identity_histogram,
      Omega.cBinFiberHist_6_2, Omega.cBinFiberHist_6_3, Omega.cBinFiberHist_6_4]
  · norm_num [conclusion_window6_degree_spectrum_capacity_tail_identity_right_derivative,
      conclusion_window6_degree_spectrum_capacity_tail_identity_tail_count,
      conclusion_window6_degree_spectrum_capacity_tail_identity_histogram,
      Omega.cBinFiberHist_6_2, Omega.cBinFiberHist_6_3, Omega.cBinFiberHist_6_4]
  · norm_num [conclusion_window6_degree_spectrum_capacity_tail_identity_right_derivative,
      conclusion_window6_degree_spectrum_capacity_tail_identity_tail_count,
      conclusion_window6_degree_spectrum_capacity_tail_identity_histogram,
      Omega.cBinFiberHist_6_2, Omega.cBinFiberHist_6_3, Omega.cBinFiberHist_6_4]
  · norm_num [conclusion_window6_degree_spectrum_capacity_tail_identity_right_derivative,
      conclusion_window6_degree_spectrum_capacity_tail_identity_tail_count,
      conclusion_window6_degree_spectrum_capacity_tail_identity_histogram,
      Omega.cBinFiberHist_6_2, Omega.cBinFiberHist_6_3, Omega.cBinFiberHist_6_4]
  · norm_num [conclusion_window6_degree_spectrum_capacity_tail_identity_right_derivative,
      conclusion_window6_degree_spectrum_capacity_tail_identity_tail_count,
      conclusion_window6_degree_spectrum_capacity_tail_identity_histogram,
      Omega.cBinFiberHist_6_2, Omega.cBinFiberHist_6_3, Omega.cBinFiberHist_6_4]

end Omega.Conclusion
