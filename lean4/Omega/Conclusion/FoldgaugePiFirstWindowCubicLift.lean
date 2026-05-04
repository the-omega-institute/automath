import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-foldgauge-pi-first-window-cubic-lift`. -/
theorem paper_conclusion_foldgauge_pi_first_window_cubic_lift (q sqrt5 K : Real)
    (hq : q = (1 + sqrt5) / 4) (hsq : sqrt5 * sqrt5 = 5) (hden : 1 - q ≠ 0)
    (hK : K = (-sqrt5 / 180) * ((q ^ 3 - q) / (1 - q))) :
    K = (3 + sqrt5) / 288 := by
  rw [hK]
  have hcancel : (q ^ 3 - q) / (1 - q) = -q * (q + 1) := by
    have hnum : q ^ 3 - q = q * (q - 1) * (q + 1) := by ring
    have hden_eq : 1 - q = -(q - 1) := by ring
    have hqm1 : q - 1 ≠ 0 := by
      intro h
      apply hden
      linarith
    rw [hnum, hden_eq]
    field_simp [hqm1]
  have hsq2 : sqrt5 ^ 2 = 5 := by
    nlinarith [hsq]
  have hsq3 : sqrt5 ^ 3 = 5 * sqrt5 := by
    calc
      sqrt5 ^ 3 = (sqrt5 * sqrt5) * sqrt5 := by ring
      _ = 5 * sqrt5 := by rw [hsq]
  rw [hcancel, hq]
  ring_nf
  rw [hsq2, hsq3]
  ring

end Omega.Conclusion
