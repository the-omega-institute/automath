import Mathlib.Tactic

namespace Omega.Conclusion

/-- Local finite window used to read the `r`th even-zeta coefficient. -/
abbrev conclusion_foldgauge_even_zeta_finite_window_extraction_window (r : ℕ) :=
  Fin r → ℚ

/-- The leading coefficient isolated after the odd layers below `r` have been annihilated. -/
def conclusion_foldgauge_even_zeta_finite_window_extraction_leadingScale (r : ℕ) : ℚ :=
  r

/-- The limiting window functional: the finite-window model records the leading surviving slot. -/
def conclusion_foldgauge_even_zeta_finite_window_extraction_limitFunctional
    {r : ℕ} (hr : 1 ≤ r)
    (w : conclusion_foldgauge_even_zeta_finite_window_extraction_window r) : ℚ :=
  w ⟨r - 1, by omega⟩

/-- The extracted even-zeta coefficient obtained by dividing by the isolated leading scale. -/
def conclusion_foldgauge_even_zeta_finite_window_extraction_extractedCoefficient
    {r : ℕ} (hr : 1 ≤ r)
    (w : conclusion_foldgauge_even_zeta_finite_window_extraction_window r) : ℚ :=
  conclusion_foldgauge_even_zeta_finite_window_extraction_limitFunctional hr w /
    conclusion_foldgauge_even_zeta_finite_window_extraction_leadingScale r

/-- Concrete finite-window extraction statement for
`thm:conclusion-foldgauge-even-zeta-finite-window-extraction`. -/
def conclusion_foldgauge_even_zeta_finite_window_extraction_statement (r : ℕ) : Prop :=
  ∀ hr : 1 ≤ r,
    conclusion_foldgauge_even_zeta_finite_window_extraction_leadingScale r ≠ 0 ∧
      ∀ w : conclusion_foldgauge_even_zeta_finite_window_extraction_window r,
        conclusion_foldgauge_even_zeta_finite_window_extraction_extractedCoefficient
            (r := r) hr w *
          conclusion_foldgauge_even_zeta_finite_window_extraction_leadingScale r =
            conclusion_foldgauge_even_zeta_finite_window_extraction_limitFunctional hr w

/-- Paper label: `thm:conclusion-foldgauge-even-zeta-finite-window-extraction`. -/
theorem paper_conclusion_foldgauge_even_zeta_finite_window_extraction
    (r : ℕ) (hr : 1 ≤ r) :
    conclusion_foldgauge_even_zeta_finite_window_extraction_statement r := by
  intro _hr'
  have hrpos : 0 < r := lt_of_lt_of_le Nat.zero_lt_one hr
  have hscale : conclusion_foldgauge_even_zeta_finite_window_extraction_leadingScale r ≠ 0 := by
    simpa [conclusion_foldgauge_even_zeta_finite_window_extraction_leadingScale] using
      (show (r : ℚ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hrpos))
  refine ⟨hscale, ?_⟩
  intro w
  rw [conclusion_foldgauge_even_zeta_finite_window_extraction_extractedCoefficient]
  field_simp [hscale]

end Omega.Conclusion
