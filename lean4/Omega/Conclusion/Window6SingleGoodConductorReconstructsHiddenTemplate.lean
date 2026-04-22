import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic
import Omega.Conclusion.Window6HiddenTemplatePrimegoodRamanujanFaultlaw

namespace Omega.Conclusion

/-- A single prime-good conductor already reconstructs the hidden template size `d ∈ {2,3,4}`
from the corresponding window-`6` Ramanujan mean. -/
theorem paper_conclusion_window6_single_good_conductor_reconstructs_hidden_template
    (q d : ℕ) (hq : Nat.Coprime q 39270) (hq2 : 2 ≤ q) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) :
    d = ((Nat.totient q : ℚ) - (ArithmeticFunction.moebius q : ℚ)) /
      (Omega.Conclusion.window6RamanujanMean q d - (ArithmeticFunction.moebius q : ℚ)) := by
  rcases paper_conclusion_window6_hidden_template_primegood_ramanujan_faultlaw q hq with
    ⟨h2, h3, h4, _⟩
  have hq_pos : 0 < q := by omega
  have htot_pos : 0 < Nat.totient q := Nat.totient_pos.mpr hq_pos
  have hq_ne_two : q ≠ 2 := by
    intro hq'
    subst hq'
    norm_num at hq
  have htot_ne_one : Nat.totient q ≠ 1 := by
    intro htot
    rcases Nat.totient_eq_one_iff.mp htot with hq' | hq'
    · omega
    · exact hq_ne_two hq'
  have hphi_sub_mu_ne :
      ((Nat.totient q : ℚ) - (ArithmeticFunction.moebius q : ℚ)) ≠ 0 := by
    rcases ArithmeticFunction.moebius_eq_or q with hμ | hμ | hμ
    · simpa [hμ] using (show (Nat.totient q : ℚ) ≠ 0 by exact_mod_cast htot_pos.ne')
    · have hcast : (Nat.totient q : ℚ) - 1 ≠ 0 := by
        intro hzero
        apply htot_ne_one
        have htot : (Nat.totient q : ℚ) = 1 := by linarith
        exact_mod_cast htot
      simpa [hμ] using hcast
    · have hpos : 0 < (Nat.totient q : ℚ) + 1 := by
        exact add_pos_of_pos_of_nonneg (by exact_mod_cast htot_pos) zero_le_one
      have hneq : (Nat.totient q : ℚ) + 1 ≠ 0 := by linarith
      simpa [hμ] using hneq
  norm_num at hd
  rcases hd with rfl | rfl | rfl
  · rw [h2]
    have hden :
        (((Nat.totient q : ℚ) + (ArithmeticFunction.moebius q : ℚ)) / 2) -
            (ArithmeticFunction.moebius q : ℚ) =
          (((Nat.totient q : ℚ) - (ArithmeticFunction.moebius q : ℚ)) / 2) := by
      ring
    rw [hden]
    field_simp [hphi_sub_mu_ne]
    ring
  · rw [h3]
    have hden :
        (((Nat.totient q : ℚ) + 2 * (ArithmeticFunction.moebius q : ℚ)) / 3) -
            (ArithmeticFunction.moebius q : ℚ) =
          (((Nat.totient q : ℚ) - (ArithmeticFunction.moebius q : ℚ)) / 3) := by
      ring
    rw [hden]
    field_simp [hphi_sub_mu_ne]
    ring
  · rw [h4]
    have hden :
        (((Nat.totient q : ℚ) + 3 * (ArithmeticFunction.moebius q : ℚ)) / 4) -
            (ArithmeticFunction.moebius q : ℚ) =
          (((Nat.totient q : ℚ) - (ArithmeticFunction.moebius q : ℚ)) / 4) := by
      ring
    rw [hden]
    field_simp [hphi_sub_mu_ne]
    ring

end Omega.Conclusion
