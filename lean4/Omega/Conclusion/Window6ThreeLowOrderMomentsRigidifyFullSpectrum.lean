import Mathlib.Tactic
import Omega.Conclusion.Window6FirstThreeMomentsRecoverWedderburnType

namespace Omega.Conclusion

private theorem window6_two_term_recurrence (q : ℕ) :
    8 * 2 ^ (q + 3) + 26 * (8 * 2 ^ (q + 1)) = 9 * (8 * 2 ^ (q + 2)) + 24 * (8 * 2 ^ q) := by
  rw [pow_add, pow_add, pow_add]
  norm_num
  ring

private theorem window6_three_term_recurrence (q : ℕ) :
    4 * 3 ^ (q + 3) + 26 * (4 * 3 ^ (q + 1)) = 9 * (4 * 3 ^ (q + 2)) + 24 * (4 * 3 ^ q) := by
  rw [pow_add, pow_add, pow_add]
  norm_num
  ring

private theorem window6_four_term_recurrence (q : ℕ) :
    9 * 4 ^ (q + 3) + 26 * (9 * 4 ^ (q + 1)) = 9 * (9 * 4 ^ (q + 2)) + 24 * (9 * 4 ^ q) := by
  rw [pow_add, pow_add, pow_add]
  norm_num
  ring

/-- Recover the window-`6` histogram `(8,4,9)` from the first three low-order moments and
rigidify the full spectrum by the cubic recurrence with roots `2,3,4`.
    thm:conclusion-window6-three-low-order-moments-rigidify-full-spectrum -/
theorem paper_conclusion_window6_three_low_order_moments_rigidify_full_spectrum
    {n2 n3 n4 : ℕ} (h0 : n2 + n3 + n4 = 21) (h1 : 2 * n2 + 3 * n3 + 4 * n4 = 64)
    (h2 : 4 * n2 + 9 * n3 + 16 * n4 = 212) :
    n2 = 8 ∧ n3 = 4 ∧ n4 = 9 ∧
      ∀ q : ℕ,
        8 * 2 ^ (q + 3) + 4 * 3 ^ (q + 3) + 9 * 4 ^ (q + 3) =
          9 * (8 * 2 ^ (q + 2) + 4 * 3 ^ (q + 2) + 9 * 4 ^ (q + 2)) -
            26 * (8 * 2 ^ (q + 1) + 4 * 3 ^ (q + 1) + 9 * 4 ^ (q + 1)) +
              24 * (8 * 2 ^ q + 4 * 3 ^ q + 9 * 4 ^ q) := by
  rcases
      paper_conclusion_window6_first_three_moments_recover_wedderburn_type h0 h1 h2
    with ⟨hn2, hn3, hn4⟩
  refine ⟨hn2, hn3, hn4, ?_⟩
  intro q
  have hbalanced :
      8 * 2 ^ (q + 3) + 4 * 3 ^ (q + 3) + 9 * 4 ^ (q + 3) +
          26 * (8 * 2 ^ (q + 1) + 4 * 3 ^ (q + 1) + 9 * 4 ^ (q + 1)) =
        9 * (8 * 2 ^ (q + 2) + 4 * 3 ^ (q + 2) + 9 * 4 ^ (q + 2)) +
          24 * (8 * 2 ^ q + 4 * 3 ^ q + 9 * 4 ^ q) := by
    nlinarith
      [window6_two_term_recurrence q, window6_three_term_recurrence q, window6_four_term_recurrence q]
  have hle :
      26 * (8 * 2 ^ (q + 1) + 4 * 3 ^ (q + 1) + 9 * 4 ^ (q + 1)) ≤
        9 * (8 * 2 ^ (q + 2) + 4 * 3 ^ (q + 2) + 9 * 4 ^ (q + 2)) := by
    rw [pow_add, pow_add, pow_add, pow_add, pow_add, pow_add]
    norm_num
    have hpow24 : 2 ^ q ≤ 4 ^ q := by
      exact Nat.pow_le_pow_left (by norm_num : 2 ≤ 4) q
    have hdom : 128 * 2 ^ q ≤ 360 * 4 ^ q := by
      calc
        128 * 2 ^ q ≤ 128 * 4 ^ q := by gcongr
        _ ≤ 360 * 4 ^ q := by
          have hnonneg : 0 ≤ 4 ^ q := Nat.zero_le _
          nlinarith
    have hnonneg3 : 0 ≤ 3 ^ q := Nat.zero_le _
    have hnonneg4 : 0 ≤ 4 ^ q := Nat.zero_le _
    nlinarith
  omega

end Omega.Conclusion
