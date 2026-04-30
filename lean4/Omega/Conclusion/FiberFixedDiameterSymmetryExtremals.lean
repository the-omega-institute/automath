import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic

namespace Omega.Conclusion

open Finset

/-- A positive weighted diameter sum forces at least one positive component multiplicity. -/
lemma conclusion_fiber_fixed_diameter_symmetry_extremals_one_le_total_multiplicity
    (D : ℕ) (m : ℕ → ℕ) (hD : 1 ≤ D)
    (hm_sum : (Finset.range (D + 1)).sum (fun l => l * m l) = D) :
    1 ≤ (Finset.range (D + 1)).sum m := by
  have hweighted_pos : 0 < (Finset.range (D + 1)).sum (fun l => l * m l) := by
    omega
  obtain ⟨l, hl, hterm⟩ :=
    (Finset.sum_pos_iff_of_nonneg
      (s := Finset.range (D + 1))
      (f := fun l => l * m l)
      (by intro l hl; exact Nat.zero_le _)).1 hweighted_pos
  have hml : 0 < m l := pos_of_mul_pos_right hterm (Nat.zero_le l)
  have hsingle : m l ≤ (Finset.range (D + 1)).sum m :=
    Finset.single_le_sum (s := Finset.range (D + 1)) (f := m)
      (by intro l hl; exact Nat.zero_le _) hl
  exact Nat.succ_le_of_lt (lt_of_lt_of_le hml hsingle)

/-- Paper label: `thm:conclusion-fiber-fixed-diameter-symmetry-extremals`. -/
theorem paper_conclusion_fiber_fixed_diameter_symmetry_extremals
    (D r : ℕ) (m : ℕ → ℕ) (hD : 1 ≤ D) (hr : r ≤ D)
    (hm_sum : (Finset.range (D + 1)).sum (fun l => l * m l) = D)
    (hm_r : (Finset.range (D + 1)).sum m = r) :
    2 ≤ 2 ^ r * (Finset.range (D + 1)).prod (fun l => (m l).factorial) ∧
      2 ^ r * (Finset.range (D + 1)).prod (fun l => (m l).factorial) ≤
        2 ^ D * D.factorial := by
  constructor
  · have hr_pos : 1 ≤ r := by
      rw [← hm_r]
      exact conclusion_fiber_fixed_diameter_symmetry_extremals_one_le_total_multiplicity
        D m hD hm_sum
    have hpow : 2 ≤ 2 ^ r := by
      simpa using (Nat.pow_le_pow_right (by norm_num : 0 < 2) hr_pos : 2 ^ 1 ≤ 2 ^ r)
    have hprod : 1 ≤ (Finset.range (D + 1)).prod (fun l => (m l).factorial) :=
      Finset.one_le_prod' (s := Finset.range (D + 1))
        (f := fun l => (m l).factorial)
        (by intro l hl; exact Nat.succ_le_of_lt (Nat.factorial_pos (m l)))
    calc
      2 = 2 * 1 := by norm_num
      _ ≤ 2 ^ r * (Finset.range (D + 1)).prod (fun l => (m l).factorial) :=
        Nat.mul_le_mul hpow hprod
  · have hpow : 2 ^ r ≤ 2 ^ D :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) hr
    have hprod_to_sum :
        (Finset.range (D + 1)).prod (fun l => (m l).factorial) ≤
          ((Finset.range (D + 1)).sum m).factorial := by
      have hdvd :
          (Finset.range (D + 1)).prod (fun l => (m l).factorial) ∣
            ((Finset.range (D + 1)).sum m).factorial := by
        simpa using
          (Nat.prod_factorial_dvd_factorial_sum (Finset.range (D + 1)) m)
      exact Nat.le_of_dvd (Nat.factorial_pos _) hdvd
    have hprod : (Finset.range (D + 1)).prod (fun l => (m l).factorial) ≤
        D.factorial := by
      calc
        (Finset.range (D + 1)).prod (fun l => (m l).factorial) ≤
            ((Finset.range (D + 1)).sum m).factorial := hprod_to_sum
        _ = r.factorial := by rw [hm_r]
        _ ≤ D.factorial := Nat.factorial_le hr
    exact Nat.mul_le_mul hpow hprod

end Omega.Conclusion
