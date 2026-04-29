import Mathlib.Tactic
import Omega.Conclusion.ShiftedHankelRigidity
import Omega.Conclusion.SpectrumSignLaw

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-golden-shifted-hankel-mod4-sign-periodicity`. -/
theorem paper_conclusion_golden_shifted_hankel_mod4_sign_periodicity (q r : Nat) :
    conclusion_shifted_hankel_rigidity_det q r (-1) =
      (if q % 4 = 0 ∨ q % 4 = 3 then (1 : Int) else (-1 : Int) ^ r) *
        conclusion_shifted_hankel_rigidity_det q 0 (-1) := by
  have htri :
      conclusion_shifted_hankel_rigidity_tri q = q * (q + 1) / 2 := by
    rw [conclusion_shifted_hankel_rigidity_tri,
      Fin.sum_univ_eq_sum_range (fun i : ℕ => i) (q + 1), Finset.sum_range_id]
    have hmul : (q + 1) * (q + 1 - 1) = q * (q + 1) := by
      rw [Nat.add_sub_cancel]
      ring
    rw [hmul]
  have hsign :
      (-1 : Int) ^ (r * conclusion_shifted_hankel_rigidity_tri q) =
        if q % 4 = 0 ∨ q % 4 = 3 then (1 : Int) else (-1 : Int) ^ r := by
    rw [htri]
    by_cases hcase : q % 4 = 0 ∨ q % 4 = 3
    · rw [if_pos hcase]
      have hbase : (-1 : Int) ^ (q * (q + 1) / 2) = 1 := by
        simpa [hcase] using neg_one_pow_triangular_mod4 q
      have hT : Even (q * (q + 1) / 2) :=
        (neg_one_pow_eq_one_iff_even (R := Int) (by decide)).mp hbase
      rcases hT with ⟨k, hk⟩
      rw [hk]
      exact Even.neg_one_pow ⟨r * k, by ring⟩
    · rw [if_neg hcase]
      have hbase : (-1 : Int) ^ (q * (q + 1) / 2) = -1 := by
        simpa [hcase] using neg_one_pow_triangular_mod4 q
      have hT : Odd (q * (q + 1) / 2) :=
        (neg_one_pow_eq_neg_one_iff_odd (R := Int) (by decide)).mp hbase
      have hparity : Even (r * (q * (q + 1) / 2)) ↔ Even r := by
        rw [Nat.even_mul]
        have hnot : ¬ Even (q * (q + 1) / 2) := (Nat.not_even_iff_odd).mpr hT
        simp [hnot]
      exact neg_one_pow_congr hparity
  calc
    conclusion_shifted_hankel_rigidity_det q r (-1) =
        (-1 : Int) ^ (r * conclusion_shifted_hankel_rigidity_tri q) *
          conclusion_shifted_hankel_rigidity_det q 0 (-1) := by
      exact paper_conclusion_shifted_hankel_rigidity q r (-1)
    _ = (if q % 4 = 0 ∨ q % 4 = 3 then (1 : Int) else (-1 : Int) ^ r) *
          conclusion_shifted_hankel_rigidity_det q 0 (-1) := by
      rw [hsign]

end Omega.Conclusion
