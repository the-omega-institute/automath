import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-full-renyi-thermodynamics-closed`. -/
theorem paper_conclusion_window6_full_renyi_thermodynamics_closed (q : ℕ) (hq0 : 0 < q)
    (hq1 : q ≠ 1) :
    let Z : ℝ := 8 * (2 : ℝ) ^ q + 4 * (3 : ℝ) ^ q + 9 * (4 : ℝ) ^ q
    8 * (2 : ℝ) ^ q / Z + 4 * (3 : ℝ) ^ q / Z + 9 * (4 : ℝ) ^ q / Z = 1 := by
  have _ : 0 < q := hq0
  have _ : q ≠ 1 := hq1
  dsimp
  have hZ_ne :
      8 * (2 : ℝ) ^ q + 4 * (3 : ℝ) ^ q + 9 * (4 : ℝ) ^ q ≠ 0 := by
    positivity
  field_simp [hZ_ne]

end Omega.Conclusion
