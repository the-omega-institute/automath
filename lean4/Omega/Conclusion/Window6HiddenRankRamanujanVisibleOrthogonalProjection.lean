import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic
import Omega.Conclusion.Window6HiddenTemplatePrimegoodRamanujanFaultlaw

namespace Omega.Conclusion

/-- Indicator of the zero exact-gcd stratum `S_21`. -/
def conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_indicator_s21
    (r : Fin 21) : ℚ :=
  if 3 ∣ r.1 ∧ 7 ∣ r.1 then 1 else 0

/-- Indicator of the exact-gcd stratum `S_3`. -/
def conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_indicator_s3
    (r : Fin 21) : ℚ :=
  if 3 ∣ r.1 ∧ ¬ 7 ∣ r.1 then 1 else 0

/-- Indicator of the exact-gcd stratum `S_7`. -/
def conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_indicator_s7
    (r : Fin 21) : ℚ :=
  if ¬ 3 ∣ r.1 ∧ 7 ∣ r.1 then 1 else 0

/-- Indicator of the exact-gcd stratum `S_1`. -/
def conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_indicator_s1
    (r : Fin 21) : ℚ :=
  if ¬ 3 ∣ r.1 ∧ ¬ 7 ∣ r.1 then 1 else 0

/-- Canonical conductor-`3` Ramanujan basis vector on the `mod 21` CRT layer. -/
def conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_c3
    (r : Fin 21) : ℚ :=
  if 3 ∣ r.1 then 2 else -1

/-- Canonical conductor-`7` Ramanujan basis vector on the `mod 21` CRT layer. -/
def conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_c7
    (r : Fin 21) : ℚ :=
  if 7 ∣ r.1 then 6 else -1

/-- Canonical conductor-`21` Ramanujan basis vector on the `mod 21` CRT layer. -/
def conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_c21
    (r : Fin 21) : ℚ :=
  conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_c3 r *
    conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_c7 r

/-- The hidden-rank neutrality average over the three multiplicity templates `d = 2, 3, 4`. -/
def conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_hidden_average
    (q : ℕ) : ℚ :=
  (window6RamanujanMean q 2 + window6RamanujanMean q 3 + window6RamanujanMean q 4) / 3

/-- The visible hidden-rank observable: away from the zero stratum only the Möbius term survives,
while the zero stratum records the hidden-multiplicity neutrality average. -/
def conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_observable
    (q : ℕ) (r : Fin 21) : ℚ :=
  if 3 ∣ r.1 ∧ 7 ∣ r.1 then
    conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_hidden_average q
  else
    ArithmeticFunction.moebius q

/-- In the finite exact-gcd model, the visible orthogonal projection is the stratum-wise averaging
operator, implemented by reconstructing from the four exact-gcd strata. -/
def conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_strata_reconstruction
    (f : Fin 21 → ℚ) : Fin 21 → ℚ :=
  fun r =>
    f 0 * conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_indicator_s21 r +
      f 3 * conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_indicator_s3 r +
      f 7 * conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_indicator_s7 r +
      f 1 * conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_indicator_s1 r

/-- In the finite exact-gcd model, the visible orthogonal projection is the stratum-wise averaging
operator, implemented by reconstructing from the four exact-gcd strata. -/
def conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_projection
    (q : ℕ) : Fin 21 → ℚ :=
  conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_strata_reconstruction
    (conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_observable q)

/-- Paper label: `thm:conclusion-window6-hidden-rank-ramanujan-visible-orthogonal-projection`.
The window-`6` hidden-rank visible projection is the exact-gcd-stratum average; the hidden
multiplicity neutrality law collapses it to a constant plus the zero-stratum indicator; and the
zero-stratum indicator is the explicit Ramanujan basis combination on the CRT layer. -/
theorem paper_conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection
    (q : ℕ) (hq : Nat.Coprime q 39270) :
    (∀ r,
      conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_projection q r =
        conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_hidden_average q *
            conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_indicator_s21 r +
          (ArithmeticFunction.moebius q : ℚ) *
            conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_indicator_s3 r +
          (ArithmeticFunction.moebius q : ℚ) *
            conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_indicator_s7 r +
          (ArithmeticFunction.moebius q : ℚ) *
            conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_indicator_s1 r) ∧
      (∀ r,
        conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_projection q r =
          (ArithmeticFunction.moebius q : ℚ) +
            ((13 : ℚ) * ((Nat.totient q : ℚ) - (ArithmeticFunction.moebius q : ℚ)) / 36) *
              conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_indicator_s21
                r) ∧
      (∀ r,
        conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_projection q r =
          (ArithmeticFunction.moebius q : ℚ) +
            ((13 : ℚ) * ((Nat.totient q : ℚ) - (ArithmeticFunction.moebius q : ℚ)) / 756) *
              (1 + conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_c3 r +
                conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_c7 r +
                conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_c21 r)) := by
  rcases paper_conclusion_window6_hidden_template_primegood_ramanujan_faultlaw q hq with
    ⟨h2, h3, h4, _⟩
  have hhidden :
      conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_hidden_average q =
        ((13 : ℚ) * (Nat.totient q : ℚ) + 23 * (ArithmeticFunction.moebius q : ℚ)) / 36 := by
    rw [conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_hidden_average, h2,
      h3, h4]
    ring
  have hshift :
      conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_hidden_average q =
        (ArithmeticFunction.moebius q : ℚ) +
          ((13 : ℚ) * ((Nat.totient q : ℚ) - (ArithmeticFunction.moebius q : ℚ)) / 36) := by
    rw [hhidden]
    ring
  have hindicator :
      ∀ r,
        conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_indicator_s21 r =
          (1 + conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_c3 r +
              conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_c7 r +
              conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_c21 r) /
            21 := by
    intro r
    fin_cases r <;>
      norm_num [conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_indicator_s21,
        conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_c3,
        conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_c7,
        conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_c21]
  have hproj_indicator :
      ∀ r,
        conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_projection q r =
          (ArithmeticFunction.moebius q : ℚ) +
            ((13 : ℚ) * ((Nat.totient q : ℚ) - (ArithmeticFunction.moebius q : ℚ)) / 36) *
              conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_indicator_s21
                r := by
    intro r
    fin_cases r <;>
      simp [conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_projection,
        conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_observable,
        conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_hidden_average,
        conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_strata_reconstruction,
        conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_indicator_s21,
        conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_indicator_s3,
        conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_indicator_s7,
        conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_indicator_s1, h2,
        h3, h4]
      <;> ring
  refine ⟨?_, hproj_indicator, ?_⟩
  · intro r
    fin_cases r <;>
      simp [conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_projection,
        conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_observable,
        conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_hidden_average,
        conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_strata_reconstruction,
        conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_indicator_s21,
        conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_indicator_s3,
        conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_indicator_s7,
        conclusion_window6_hidden_rank_ramanujan_visible_orthogonal_projection_indicator_s1]
  · intro r
    rw [hproj_indicator r, hindicator r]
    ring

end Omega.Conclusion
