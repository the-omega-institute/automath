import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label:
`prop:conclusion-window6-all-good-odd-conductors-strictly-positive`. -/
theorem paper_conclusion_window6_all_good_odd_conductors_strictly_positive
    {X : Type} (R : X → Nat → Int) (d : X → Nat) (mu : Nat → Int) (phi q : Nat)
    (hphi : 12 ≤ phi) (hmu_low : -1 ≤ mu q) (hmu_high : mu q ≤ 1)
    (hdpos : ∀ w, 0 < d w) (hdle : ∀ w, d w ≤ 4)
    (hformula : ∀ w, (d w : Int) * R w q = (phi : Int) + ((d w : Int) - 1) * mu q) :
    ∀ w, 0 < R w q := by
  intro w
  have hphiInt : (12 : Int) ≤ (phi : Int) := by
    exact_mod_cast hphi
  have hmu_high_used : mu q ≤ 1 := hmu_high
  have hd_cases : d w = 1 ∨ d w = 2 ∨ d w = 3 ∨ d w = 4 := by
    have hdposw := hdpos w
    have hdlew := hdle w
    omega
  rcases hd_cases with hd | hd | hd | hd
  · have hform := hformula w
    rw [hd] at hform
    norm_num at hform
    nlinarith [hphiInt, hmu_low, hmu_high_used]
  · have hform := hformula w
    rw [hd] at hform
    norm_num at hform
    nlinarith [hphiInt, hmu_low, hmu_high_used]
  · have hform := hformula w
    rw [hd] at hform
    norm_num at hform
    nlinarith [hphiInt, hmu_low, hmu_high_used]
  · have hform := hformula w
    rw [hd] at hform
    norm_num at hform
    nlinarith [hphiInt, hmu_low, hmu_high_used]

end Omega.Conclusion
