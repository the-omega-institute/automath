import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

noncomputable section

/-- The fixed contraction ratio `q = φ / 2` appearing in the odd-power asymptotic tower. -/
def conclusion_foldgauge_pi_evenzeta_first_difference_q : ℝ :=
  Real.goldenRatio / 2

/-- The odd-power scale `q^{(2j-1)m}` at level `j`. -/
def conclusion_foldgauge_pi_evenzeta_first_difference_odd_scale (j m : ℕ) : ℝ :=
  conclusion_foldgauge_pi_evenzeta_first_difference_q ^ ((2 * j - 1) * m)

/-- The order-`r` truncation of the odd-power expansion. -/
def conclusion_foldgauge_pi_evenzeta_first_difference_partial_sum
    (coeff : ℕ → ℝ) (r m : ℕ) : ℝ :=
  Finset.sum (Finset.range r) fun j =>
    coeff (j + 1) * conclusion_foldgauge_pi_evenzeta_first_difference_odd_scale (j + 1) m

/-- The remainder scale after truncation at order `r`. -/
def conclusion_foldgauge_pi_evenzeta_first_difference_remainder_scale (r m : ℕ) : ℝ :=
  conclusion_foldgauge_pi_evenzeta_first_difference_q ^ ((2 * r + 1) * m)

lemma conclusion_foldgauge_pi_evenzeta_first_difference_partial_sum_sub
    {r : ℕ} (hr : 1 ≤ r) (a b : ℕ → ℝ) (m : ℕ)
    (hcoeff : ∀ j, 1 ≤ j → j < r → a j = b j) :
    conclusion_foldgauge_pi_evenzeta_first_difference_partial_sum a r m -
        conclusion_foldgauge_pi_evenzeta_first_difference_partial_sum b r m =
      (a r - b r) * conclusion_foldgauge_pi_evenzeta_first_difference_odd_scale r m := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hr) with ⟨k, rfl⟩
  have hsum :
      Finset.sum (Finset.range k) (fun j =>
          a (j + 1) * conclusion_foldgauge_pi_evenzeta_first_difference_odd_scale (j + 1) m) =
        Finset.sum (Finset.range k) (fun j =>
          b (j + 1) * conclusion_foldgauge_pi_evenzeta_first_difference_odd_scale (j + 1) m) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt : j + 1 < k + 1 := Nat.succ_lt_succ (Finset.mem_range.mp hj)
    have hEq : a (j + 1) = b (j + 1) := hcoeff (j + 1) (Nat.succ_le_succ (Nat.zero_le _)) hjlt
    simp [hEq]
  calc
    conclusion_foldgauge_pi_evenzeta_first_difference_partial_sum a (k + 1) m -
        conclusion_foldgauge_pi_evenzeta_first_difference_partial_sum b (k + 1) m =
      ((Finset.sum (Finset.range k) fun j =>
            a (j + 1) * conclusion_foldgauge_pi_evenzeta_first_difference_odd_scale (j + 1) m) +
          a (k + 1) * conclusion_foldgauge_pi_evenzeta_first_difference_odd_scale (k + 1) m) -
        ((Finset.sum (Finset.range k) fun j =>
              b (j + 1) * conclusion_foldgauge_pi_evenzeta_first_difference_odd_scale (j + 1) m) +
            b (k + 1) * conclusion_foldgauge_pi_evenzeta_first_difference_odd_scale (k + 1) m) := by
          simp [conclusion_foldgauge_pi_evenzeta_first_difference_partial_sum,
            Finset.sum_range_succ]
    _ = (a (k + 1) - b (k + 1)) *
          conclusion_foldgauge_pi_evenzeta_first_difference_odd_scale (k + 1) m := by
          rw [hsum]
          ring

/-- Paper label: `thm:conclusion-foldgauge-pi-evenzeta-first-difference`. If two `log`-side
odd-power expansions agree through level `r - 1`, then subtracting them cancels those terms and
the first nonzero difference occurs at the surviving order `r`. -/
theorem paper_conclusion_foldgauge_pi_evenzeta_first_difference
    (r : ℕ) (hr : 1 ≤ r) (logC logCtilde a atilde rem remtilde : ℕ → ℝ)
    (hC : ∀ m,
      logC m =
        Real.log (2 * Real.pi) +
          conclusion_foldgauge_pi_evenzeta_first_difference_partial_sum a r m +
            rem m * conclusion_foldgauge_pi_evenzeta_first_difference_remainder_scale r m)
    (hCt : ∀ m,
      logCtilde m =
        Real.log (2 * Real.pi) +
          conclusion_foldgauge_pi_evenzeta_first_difference_partial_sum atilde r m +
            remtilde m * conclusion_foldgauge_pi_evenzeta_first_difference_remainder_scale r m)
    (hcoeff : ∀ j, 1 ≤ j → j < r → a j = atilde j)
    (hrdiff : a r ≠ atilde r) :
    (∀ m,
      logC m - logCtilde m =
        (a r - atilde r) * conclusion_foldgauge_pi_evenzeta_first_difference_odd_scale r m +
          (rem m - remtilde m) *
            conclusion_foldgauge_pi_evenzeta_first_difference_remainder_scale r m) ∧
      a r - atilde r ≠ 0 := by
  refine ⟨?_, sub_ne_zero.mpr hrdiff⟩
  intro m
  rw [hC m, hCt m]
  have hmain :=
    conclusion_foldgauge_pi_evenzeta_first_difference_partial_sum_sub hr a atilde m hcoeff
  calc
    (Real.log (2 * Real.pi) +
          conclusion_foldgauge_pi_evenzeta_first_difference_partial_sum a r m +
            rem m * conclusion_foldgauge_pi_evenzeta_first_difference_remainder_scale r m) -
        (Real.log (2 * Real.pi) +
          conclusion_foldgauge_pi_evenzeta_first_difference_partial_sum atilde r m +
            remtilde m * conclusion_foldgauge_pi_evenzeta_first_difference_remainder_scale r m) =
      (conclusion_foldgauge_pi_evenzeta_first_difference_partial_sum a r m -
            conclusion_foldgauge_pi_evenzeta_first_difference_partial_sum atilde r m) +
          (rem m - remtilde m) *
            conclusion_foldgauge_pi_evenzeta_first_difference_remainder_scale r m := by
          ring
    _ = (a r - atilde r) * conclusion_foldgauge_pi_evenzeta_first_difference_odd_scale r m +
          (rem m - remtilde m) *
            conclusion_foldgauge_pi_evenzeta_first_difference_remainder_scale r m := by
          rw [hmain]

end

end Omega.Conclusion
