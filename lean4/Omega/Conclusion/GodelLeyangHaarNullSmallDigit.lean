import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-godel-leyang-haar-null-small-digit`. -/
theorem paper_conclusion_godel_leyang_haar_null_small_digit
    (B digitMass haarMass : ℝ) (hB : 0 < B) (hsmall : digitMass < B ^ 2)
    (hnonneg : 0 ≤ haarMass)
    (hself : haarMass ≤ digitMass * (B ^ 2)⁻¹ * haarMass) :
    haarMass = 0 := by
  have hBsq_pos : 0 < B ^ 2 := pow_pos hB 2
  have hcoeff_lt : digitMass * (B ^ 2)⁻¹ < 1 := by
    have hmul := mul_lt_mul_of_pos_right hsmall (inv_pos.mpr hBsq_pos)
    simpa [mul_inv_cancel₀ (ne_of_gt hBsq_pos)] using hmul
  by_contra hne
  have hpos : 0 < haarMass := lt_of_le_of_ne hnonneg (Ne.symm hne)
  have hstrict : digitMass * (B ^ 2)⁻¹ * haarMass < haarMass := by
    have hmul := mul_lt_mul_of_pos_right hcoeff_lt hpos
    simpa [mul_assoc] using hmul
  exact (not_le_of_gt hstrict) hself

end Omega.Conclusion
