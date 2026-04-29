import Mathlib.Tactic
import Omega.Conclusion.Window6Collision

namespace Omega.Conclusion

/-- Invert the first three moment equations on the support `{2,3,4}`.
    thm:conclusion-window6-three-moment-spectrum-inversion -/
theorem paper_conclusion_window6_three_moment_spectrum_inversion
    (S0 S1 S2 N2 N3 N4 : ℤ)
    (h0 : S0 = N2 + N3 + N4)
    (h1 : S1 = 2 * N2 + 3 * N3 + 4 * N4)
    (h2 : S2 = 4 * N2 + 9 * N3 + 16 * N4) :
    N2 = (12 * S0 - 7 * S1 + S2) / 2 ∧
      N3 = -8 * S0 + 6 * S1 - S2 ∧
      N4 = (6 * S0 - 5 * S1 + S2) / 2 := by
  have hN2 : 12 * S0 - 7 * S1 + S2 = 2 * N2 := by
    nlinarith [h0, h1, h2]
  have hN3 : -8 * S0 + 6 * S1 - S2 = N3 := by
    nlinarith [h0, h1, h2]
  have hN4 : 6 * S0 - 5 * S1 + S2 = 2 * N4 := by
    nlinarith [h0, h1, h2]
  refine ⟨?_, ?_, ?_⟩
  · rw [hN2]
    simpa using (Int.ediv_mul_cancel (show (2 : ℤ) ∣ 2 * N2 by exact dvd_mul_right _ _)).symm
  · exact hN3.symm
  · rw [hN4]
    simpa using (Int.ediv_mul_cancel (show (2 : ℤ) ∣ 2 * N4 by exact dvd_mul_right _ _)).symm

/-- Window-6 specialization recovers the histogram `(8,4,9)` from `(S0,S1,S2) = (21,64,212)`. -/
theorem window6_three_moment_spectrum_histogram :
    ((12 * (21 : ℤ) - 7 * 64 + 212) / 2 = 8) ∧
      (-8 * (21 : ℤ) + 6 * 64 - 212 = 4) ∧
      ((6 * (21 : ℤ) - 5 * 64 + 212) / 2 = 9) := by
  have htriple := window6_qmoment_triple
  rcases htriple with ⟨h0, h1, h2⟩
  have hinv :=
    paper_conclusion_window6_three_moment_spectrum_inversion
      21 64 212 8 4 9 (by simpa using h0) (by simpa using h1) (by simpa using h2)
  simpa using hinv

/-- The concrete window-6 Wedderburn second moment matches the same recovered histogram. -/
theorem window6_three_moment_spectrum_wedderburn :
    4 * (8 : ℤ) + 9 * 4 + 16 * 9 = 212 := by
  norm_num

private lemma rat_div_eq_int_div_of_dvd (a b : ℤ) (hb : b ≠ 0) (hdiv : b ∣ a) :
    ((a : ℚ) / b) = (a / b : ℤ) := by
  have hbQ : (b : ℚ) ≠ 0 := by
    exact_mod_cast hb
  apply (div_eq_iff hbQ).2
  have hmul : (((a / b : ℤ) : ℚ) * (b : ℚ)) = (a : ℚ) := by
    exact_mod_cast (Int.ediv_mul_cancel hdiv)
  simpa using hmul.symm

/-- Congruence characterization of the integral image of the diagonal second-moment inversion. -/
theorem paper_conclusion_window6_cyclic_multiplicity_secondmoment_lattice_inversion (A B C : ℤ) :
    let f2 : ℚ := (-2 * A + B + 2 * C) / 10
    let f3 : ℚ := (8 * A - 9 * B + 7 * C) / 60
    let f4 : ℚ := (4 * A + 3 * B - 4 * C) / 30
    ((A - C) % 3 = 0 ∧ (4 * A - 3 * B - C) % 12 = 0 ∧ (-2 * A + B + 2 * C) % 10 = 0) ↔
      ∃ n2 n3 n4 : ℤ, f2 = n2 ∧ f3 = n3 ∧ f4 = n4 := by
  dsimp
  constructor
  · rintro ⟨hAC, hmid, hbase⟩
    have hdiv2 : (10 : ℤ) ∣ -2 * A + B + 2 * C := Int.dvd_of_emod_eq_zero hbase
    have hdiv3 : (12 : ℤ) ∣ 4 * A - 3 * B - C := Int.dvd_of_emod_eq_zero hmid
    have hdiv4 : (3 : ℤ) ∣ A - C := Int.dvd_of_emod_eq_zero hAC
    have h2rat : (-2 * (A : ℚ) + B + 2 * C) / 10 = (((-2 * A + B + 2 * C) / 10 : ℤ) : ℚ) := by
      simpa using rat_div_eq_int_div_of_dvd (-2 * A + B + 2 * C) 10 (by decide) hdiv2
    have h3rat : (4 * (A : ℚ) - 3 * B - C) / 12 = (((4 * A - 3 * B - C) / 12 : ℤ) : ℚ) := by
      simpa using rat_div_eq_int_div_of_dvd (4 * A - 3 * B - C) 12 (by decide) hdiv3
    have h4rat : ((A : ℚ) - C) / 3 = (((A - C) / 3 : ℤ) : ℚ) := by
      simpa using rat_div_eq_int_div_of_dvd (A - C) 3 (by decide) hdiv4
    refine ⟨(-2 * A + B + 2 * C) / 10, (-2 * A + B + 2 * C) / 10 + (4 * A - 3 * B - C) / 12,
      (-2 * A + B + 2 * C) / 10 + (A - C) / 3, ?_, ?_, ?_⟩
    · exact h2rat
    · calc
        (8 * (A : ℚ) - 9 * B + 7 * C) / 60 = (-2 * (A : ℚ) + B + 2 * C) / 10 + (4 * A - 3 * B - C) / 12 := by
          ring
        _ = (((-2 * A + B + 2 * C) / 10 : ℤ) : ℚ) + (((4 * A - 3 * B - C) / 12 : ℤ) : ℚ) := by
          rw [h2rat, h3rat]
        _ = (((-2 * A + B + 2 * C) / 10 + (4 * A - 3 * B - C) / 12 : ℤ) : ℚ) := by
          norm_num
    · calc
        (4 * (A : ℚ) + 3 * B - 4 * C) / 30 = (-2 * (A : ℚ) + B + 2 * C) / 10 + ((A : ℚ) - C) / 3 := by
          ring
        _ = (((-2 * A + B + 2 * C) / 10 : ℤ) : ℚ) + (((A - C) / 3 : ℤ) : ℚ) := by
          rw [h2rat, h4rat]
        _ = (((-2 * A + B + 2 * C) / 10 + (A - C) / 3 : ℤ) : ℚ) := by
          norm_num
  · rintro ⟨n2, n3, n4, hf2, hf3, hf4⟩
    have hbaseMulQ : -2 * (A : ℚ) + B + 2 * C = (n2 : ℚ) * 10 := by
      exact (div_eq_iff (by norm_num : (10 : ℚ) ≠ 0)).1 hf2
    have hbaseMul : -2 * A + B + 2 * C = n2 * 10 := by
      exact_mod_cast hbaseMulQ
    have hbaseDiv : (10 : ℤ) ∣ -2 * A + B + 2 * C := by
      refine ⟨n2, ?_⟩
      simpa [mul_comm] using hbaseMul
    have hmidQ : (4 * (A : ℚ) - 3 * B - C) / 12 = (n3 - n2 : ℤ) := by
      calc
        (4 * (A : ℚ) - 3 * B - C) / 12 = (8 * (A : ℚ) - 9 * B + 7 * C) / 60 - (-2 * (A : ℚ) + B + 2 * C) / 10 := by
          ring
        _ = (n3 : ℚ) - n2 := by rw [hf3, hf2]
        _ = ((n3 - n2 : ℤ) : ℚ) := by norm_num
    have hmidMulQ : 4 * (A : ℚ) - 3 * B - C = ((n3 - n2 : ℤ) : ℚ) * 12 := by
      exact (div_eq_iff (by norm_num : (12 : ℚ) ≠ 0)).1 hmidQ
    have hmidMul : 4 * A - 3 * B - C = (n3 - n2) * 12 := by
      exact_mod_cast hmidMulQ
    have hmidDiv : (12 : ℤ) ∣ 4 * A - 3 * B - C := by
      refine ⟨n3 - n2, ?_⟩
      simpa [mul_comm] using hmidMul
    have hACQ : ((A : ℚ) - C) / 3 = (n4 - n2 : ℤ) := by
      calc
        ((A : ℚ) - C) / 3 = (4 * (A : ℚ) + 3 * B - 4 * C) / 30 - (-2 * (A : ℚ) + B + 2 * C) / 10 := by
          ring
        _ = (n4 : ℚ) - n2 := by rw [hf4, hf2]
        _ = ((n4 - n2 : ℤ) : ℚ) := by norm_num
    have hACMulQ : (A : ℚ) - C = ((n4 - n2 : ℤ) : ℚ) * 3 := by
      exact (div_eq_iff (by norm_num : (3 : ℚ) ≠ 0)).1 hACQ
    have hACMul : A - C = (n4 - n2) * 3 := by
      exact_mod_cast hACMulQ
    have hACDiv : (3 : ℤ) ∣ A - C := by
      refine ⟨n4 - n2, ?_⟩
      simpa [mul_comm] using hACMul
    exact ⟨Int.emod_eq_zero_of_dvd hACDiv, Int.emod_eq_zero_of_dvd hmidDiv,
      Int.emod_eq_zero_of_dvd hbaseDiv⟩

end Omega.Conclusion
