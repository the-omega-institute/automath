import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic
import Omega.Conclusion.Window6HiddenRankRamanujanVisibleOrthogonalProjection

namespace Omega.Conclusion

/-- The three squarefree nontrivial Ramanujan conductors visible on the CRT layer modulo `21`. -/
def conclusion_window6_nontrivial_conductor_unit_ramanujan_law_nontrivial_conductor
    (q : ℕ) : Prop :=
  q = 3 ∨ q = 7 ∨ q = 21

/-- The finite CRT-layer Ramanujan character for conductors `3`, `7`, and `21`. -/
def conclusion_window6_nontrivial_conductor_unit_ramanujan_law_ramanujan
    (q : ℕ) (r : Fin 21) : ℚ :=
  if q = 3 then
    conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_c3 r
  else if q = 7 then
    conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_c7 r
  else if q = 21 then
    conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_c21 r
  else
    0

/-- Unit-weight window sum of a finite Ramanujan character on the `mod 21` layer. -/
def conclusion_window6_nontrivial_conductor_unit_ramanujan_law_unit_sum (q : ℕ) : ℚ :=
  ∑ r : Fin 21, conclusion_window6_nontrivial_conductor_unit_ramanujan_law_ramanujan q r

/-- The projected window-`6` degree profile `P_21 d = 3 + 1_{S_21}`. -/
def conclusion_window6_nontrivial_conductor_unit_ramanujan_law_degree_weight
    (r : Fin 21) : ℚ :=
  3 + conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_indicator_s21 r

/-- The projected hidden-rank profile `P_21 h = 2 + 1_{S_21}`. -/
def conclusion_window6_nontrivial_conductor_unit_ramanujan_law_hidden_weight
    (r : Fin 21) : ℚ :=
  2 + conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_indicator_s21 r

/-- Window sum of the projected degree profile against the conductor `q` Ramanujan character. -/
def conclusion_window6_nontrivial_conductor_unit_ramanujan_law_degree_sum (q : ℕ) : ℚ :=
  ∑ r : Fin 21,
    conclusion_window6_nontrivial_conductor_unit_ramanujan_law_degree_weight r *
      conclusion_window6_nontrivial_conductor_unit_ramanujan_law_ramanujan q r

/-- Window sum of the projected hidden-rank profile against the conductor `q` Ramanujan
character. -/
def conclusion_window6_nontrivial_conductor_unit_ramanujan_law_hidden_sum (q : ℕ) : ℚ :=
  ∑ r : Fin 21,
    conclusion_window6_nontrivial_conductor_unit_ramanujan_law_hidden_weight r *
      conclusion_window6_nontrivial_conductor_unit_ramanujan_law_ramanujan q r

/-- Hidden-rank squarefree Ramanujan fingerprint, with the three nontrivial conductors normalized
by their Euler factors. -/
def conclusion_window6_nontrivial_conductor_unit_ramanujan_law_hidden_rank_fingerprint
    (s : ℕ) : ℚ :=
  (1 : ℚ) / (3 : ℚ) ^ s + (1 : ℚ) / (7 : ℚ) ^ s + (1 : ℚ) / (21 : ℚ) ^ s

/-- Paper label: `cor:conclusion-window6-nontrivial-conductor-unit-ramanujan-law`.
The three nontrivial squarefree conductors on the window-`6` CRT layer have zero unit-weight
mean, are mutually orthogonal, have the expected Euler norms, and their normalized hidden-rank
fingerprint is the closed squarefree expression. -/
theorem paper_conclusion_window6_nontrivial_conductor_unit_ramanujan_law :
    (∀ q,
        conclusion_window6_nontrivial_conductor_unit_ramanujan_law_nontrivial_conductor q →
          conclusion_window6_nontrivial_conductor_unit_ramanujan_law_degree_sum q =
            (Nat.totient q : ℚ)) ∧
      (∀ q,
        conclusion_window6_nontrivial_conductor_unit_ramanujan_law_nontrivial_conductor q →
          conclusion_window6_nontrivial_conductor_unit_ramanujan_law_hidden_sum q =
            (Nat.totient q : ℚ)) ∧
      (∀ q,
        conclusion_window6_nontrivial_conductor_unit_ramanujan_law_nontrivial_conductor q →
          conclusion_window6_nontrivial_conductor_unit_ramanujan_law_unit_sum q = 0) ∧
      (∑ r : Fin 21,
          conclusion_window6_nontrivial_conductor_unit_ramanujan_law_ramanujan 3 r *
            conclusion_window6_nontrivial_conductor_unit_ramanujan_law_ramanujan 7 r) = 0 ∧
      (∑ r : Fin 21,
          conclusion_window6_nontrivial_conductor_unit_ramanujan_law_ramanujan 3 r *
            conclusion_window6_nontrivial_conductor_unit_ramanujan_law_ramanujan 21 r) = 0 ∧
      (∑ r : Fin 21,
          conclusion_window6_nontrivial_conductor_unit_ramanujan_law_ramanujan 7 r *
            conclusion_window6_nontrivial_conductor_unit_ramanujan_law_ramanujan 21 r) = 0 ∧
      (∑ r : Fin 21,
          conclusion_window6_nontrivial_conductor_unit_ramanujan_law_ramanujan 3 r *
            conclusion_window6_nontrivial_conductor_unit_ramanujan_law_ramanujan 3 r) = 42 ∧
      (∑ r : Fin 21,
          conclusion_window6_nontrivial_conductor_unit_ramanujan_law_ramanujan 7 r *
            conclusion_window6_nontrivial_conductor_unit_ramanujan_law_ramanujan 7 r) = 126 ∧
      (∑ r : Fin 21,
          conclusion_window6_nontrivial_conductor_unit_ramanujan_law_ramanujan 21 r *
            conclusion_window6_nontrivial_conductor_unit_ramanujan_law_ramanujan 21 r) = 252 ∧
      ∀ s,
        conclusion_window6_nontrivial_conductor_unit_ramanujan_law_hidden_rank_fingerprint s =
          (1 : ℚ) / (3 : ℚ) ^ s + (1 : ℚ) / (7 : ℚ) ^ s +
            (1 : ℚ) / (21 : ℚ) ^ s := by
  have hunit3 :
      conclusion_window6_nontrivial_conductor_unit_ramanujan_law_unit_sum 3 = 0 := by
    native_decide
  have hunit7 :
      conclusion_window6_nontrivial_conductor_unit_ramanujan_law_unit_sum 7 = 0 := by
    native_decide
  have hunit21 :
      conclusion_window6_nontrivial_conductor_unit_ramanujan_law_unit_sum 21 = 0 := by
    native_decide
  have hdegree3 :
      conclusion_window6_nontrivial_conductor_unit_ramanujan_law_degree_sum 3 =
        (Nat.totient 3 : ℚ) := by
    native_decide
  have hdegree7 :
      conclusion_window6_nontrivial_conductor_unit_ramanujan_law_degree_sum 7 =
        (Nat.totient 7 : ℚ) := by
    native_decide
  have hdegree21 :
      conclusion_window6_nontrivial_conductor_unit_ramanujan_law_degree_sum 21 =
        (Nat.totient 21 : ℚ) := by
    native_decide
  have hhidden3 :
      conclusion_window6_nontrivial_conductor_unit_ramanujan_law_hidden_sum 3 =
        (Nat.totient 3 : ℚ) := by
    native_decide
  have hhidden7 :
      conclusion_window6_nontrivial_conductor_unit_ramanujan_law_hidden_sum 7 =
        (Nat.totient 7 : ℚ) := by
    native_decide
  have hhidden21 :
      conclusion_window6_nontrivial_conductor_unit_ramanujan_law_hidden_sum 21 =
        (Nat.totient 21 : ℚ) := by
    native_decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    rcases hq with rfl | rfl | rfl
    · exact hdegree3
    · exact hdegree7
    · exact hdegree21
  · intro q hq
    rcases hq with rfl | rfl | rfl
    · exact hhidden3
    · exact hhidden7
    · exact hhidden21
  · intro q hq
    rcases hq with rfl | rfl | rfl
    · exact hunit3
    · exact hunit7
    · exact hunit21
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · intro s
    rfl

end Omega.Conclusion
