import Mathlib.Tactic

namespace Omega.Conclusion

/-- Indicator of the exact-gcd stratum `S_21`, represented in the `mod 21` CRT model by the
residue classes divisible by both `3` and `7`. -/
def conclusion_window6_ramanujan_sector_algebra_on_crt_layer_indicator_s21 (r : Fin 21) : ℚ :=
  if 3 ∣ r.1 ∧ 7 ∣ r.1 then 1 else 0

/-- Indicator of the exact-gcd stratum `S_3`. -/
def conclusion_window6_ramanujan_sector_algebra_on_crt_layer_indicator_s3 (r : Fin 21) : ℚ :=
  if 3 ∣ r.1 ∧ ¬ 7 ∣ r.1 then 1 else 0

/-- Indicator of the exact-gcd stratum `S_7`. -/
def conclusion_window6_ramanujan_sector_algebra_on_crt_layer_indicator_s7 (r : Fin 21) : ℚ :=
  if ¬ 3 ∣ r.1 ∧ 7 ∣ r.1 then 1 else 0

/-- Indicator of the exact-gcd stratum `S_1`. -/
def conclusion_window6_ramanujan_sector_algebra_on_crt_layer_indicator_s1 (r : Fin 21) : ℚ :=
  if ¬ 3 ∣ r.1 ∧ ¬ 7 ∣ r.1 then 1 else 0

/-- Reconstruction of a stratum-constant function from its four exact-gcd values. -/
def conclusion_window6_ramanujan_sector_algebra_on_crt_layer_strata_reconstruction
    (f : Fin 21 → ℚ) : Fin 21 → ℚ :=
  fun r =>
    f 0 * conclusion_window6_ramanujan_sector_algebra_on_crt_layer_indicator_s21 r +
      f 3 * conclusion_window6_ramanujan_sector_algebra_on_crt_layer_indicator_s3 r +
      f 7 * conclusion_window6_ramanujan_sector_algebra_on_crt_layer_indicator_s7 r +
      f 1 * conclusion_window6_ramanujan_sector_algebra_on_crt_layer_indicator_s1 r

/-- Concrete `mod 21` Ramanujan-sector data. The fields record the standard squarefree values of
`c_3`, `c_7`, and the multiplicative identity `c_21 = c_3 c_7`. -/
structure conclusion_window6_ramanujan_sector_algebra_on_crt_layer_data where
  c3 : Fin 21 → ℚ
  c7 : Fin 21 → ℚ
  c21 : Fin 21 → ℚ
  hc3 : ∀ r, c3 r = if 3 ∣ r.1 then 2 else -1
  hc7 : ∀ r, c7 r = if 7 ∣ r.1 then 6 else -1
  hc21 : ∀ r, c21 r = c3 r * c7 r

/-- Closed formula for the `S_21` indicator in the Ramanujan basis. -/
def conclusion_window6_ramanujan_sector_algebra_on_crt_layer_data.indicator_s21_formula
    (h : conclusion_window6_ramanujan_sector_algebra_on_crt_layer_data) : Prop :=
  ∀ r,
    conclusion_window6_ramanujan_sector_algebra_on_crt_layer_indicator_s21 r =
      (1 + h.c3 r + h.c7 r + h.c21 r) / 21

/-- Closed formula for the `S_3` indicator in the Ramanujan basis. -/
def conclusion_window6_ramanujan_sector_algebra_on_crt_layer_data.indicator_s3_formula
    (h : conclusion_window6_ramanujan_sector_algebra_on_crt_layer_data) : Prop :=
  ∀ r,
    conclusion_window6_ramanujan_sector_algebra_on_crt_layer_indicator_s3 r =
      (6 + 6 * h.c3 r - h.c7 r - h.c21 r) / 21

/-- Closed formula for the `S_7` indicator in the Ramanujan basis. -/
def conclusion_window6_ramanujan_sector_algebra_on_crt_layer_data.indicator_s7_formula
    (h : conclusion_window6_ramanujan_sector_algebra_on_crt_layer_data) : Prop :=
  ∀ r,
    conclusion_window6_ramanujan_sector_algebra_on_crt_layer_indicator_s7 r =
      (2 - h.c3 r + 2 * h.c7 r - h.c21 r) / 21

/-- Closed formula for the `S_1` indicator in the Ramanujan basis. -/
def conclusion_window6_ramanujan_sector_algebra_on_crt_layer_data.indicator_s1_formula
    (h : conclusion_window6_ramanujan_sector_algebra_on_crt_layer_data) : Prop :=
  ∀ r,
    conclusion_window6_ramanujan_sector_algebra_on_crt_layer_indicator_s1 r =
      (12 - 6 * h.c3 r - 2 * h.c7 r + h.c21 r) / 21

/-- The Ramanujan indicators span exactly the functions reconstructed from the four exact-gcd
strata. -/
def conclusion_window6_ramanujan_sector_algebra_on_crt_layer_data.strata_algebra_characterization
    (_h : conclusion_window6_ramanujan_sector_algebra_on_crt_layer_data) : Prop :=
  ∀ f : Fin 21 → ℚ,
    (∃ a21 a3 a7 a1 : ℚ,
      f =
        fun r =>
          a21 * conclusion_window6_ramanujan_sector_algebra_on_crt_layer_indicator_s21 r +
            a3 * conclusion_window6_ramanujan_sector_algebra_on_crt_layer_indicator_s3 r +
            a7 * conclusion_window6_ramanujan_sector_algebra_on_crt_layer_indicator_s7 r +
            a1 * conclusion_window6_ramanujan_sector_algebra_on_crt_layer_indicator_s1 r) ↔
      f = conclusion_window6_ramanujan_sector_algebra_on_crt_layer_strata_reconstruction f

/-- Paper label:
`thm:conclusion-window6-ramanujan-sector-algebra-on-crt-layer`. In the finite CRT model mod `21`,
the four exact-gcd indicators are explicit linear combinations of `1`, `c_3`, `c_7`, and
`c_21 = c_3 c_7`, and these indicators reconstruct exactly the stratum-constant function algebra.
-/
theorem paper_conclusion_window6_ramanujan_sector_algebra_on_crt_layer
    (h : conclusion_window6_ramanujan_sector_algebra_on_crt_layer_data) :
    h.indicator_s21_formula ∧ h.indicator_s3_formula ∧ h.indicator_s7_formula ∧
      h.indicator_s1_formula ∧ h.strata_algebra_characterization := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r
    fin_cases r <;>
      norm_num [conclusion_window6_ramanujan_sector_algebra_on_crt_layer_indicator_s21, h.hc3,
        h.hc7, h.hc21]
  · intro r
    fin_cases r <;>
      norm_num [conclusion_window6_ramanujan_sector_algebra_on_crt_layer_indicator_s3, h.hc3,
        h.hc7, h.hc21]
  · intro r
    fin_cases r <;>
      norm_num [conclusion_window6_ramanujan_sector_algebra_on_crt_layer_indicator_s7, h.hc3,
        h.hc7, h.hc21]
  · intro r
    fin_cases r <;>
      norm_num [conclusion_window6_ramanujan_sector_algebra_on_crt_layer_indicator_s1, h.hc3,
        h.hc7, h.hc21]
  · intro f
    constructor
    · rintro ⟨a21, a3, a7, a1, rfl⟩
      ext r
      fin_cases r <;>
        norm_num [conclusion_window6_ramanujan_sector_algebra_on_crt_layer_strata_reconstruction,
          conclusion_window6_ramanujan_sector_algebra_on_crt_layer_indicator_s21,
          conclusion_window6_ramanujan_sector_algebra_on_crt_layer_indicator_s3,
          conclusion_window6_ramanujan_sector_algebra_on_crt_layer_indicator_s7,
          conclusion_window6_ramanujan_sector_algebra_on_crt_layer_indicator_s1]
    · intro hf
      refine ⟨f 0, f 3, f 7, f 1, ?_⟩
      ext r
      simpa [conclusion_window6_ramanujan_sector_algebra_on_crt_layer_strata_reconstruction] using
        congrFun hf r

end Omega.Conclusion
