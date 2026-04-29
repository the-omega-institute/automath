import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-weyl-toeplitz-depth-three-termination`. -/
theorem paper_conclusion_window6_weyl_toeplitz_depth_three_termination
    (d r : ℕ) (rank : ℕ → ℕ) (locked : Prop) (hd : d ≤ 6)
    (hrtri : r * (r + 1) / 2 ≤ d) (hrpos : 1 ≤ r)
    (hrank : ∀ n, r - 1 ≤ n → rank n = r) (hlock : rank 3 = rank 2 → locked) :
    ∃ r0 : ℕ, r0 = r ∧ r0 ≤ 3 ∧ rank 3 = rank 2 ∧ locked := by
  have hrle3 : r ≤ 3 := by
    by_contra hnot
    have h4 : 4 ≤ r := by omega
    have h20 : 20 ≤ r * (r + 1) := by nlinarith
    have h10 : 10 ≤ r * (r + 1) / 2 :=
      (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 (by simpa using h20)
    omega
  have hrank2 : rank 2 = r := hrank 2 (by omega)
  have hrank3 : rank 3 = r := hrank 3 (by omega)
  have heq : rank 3 = rank 2 := by rw [hrank3, hrank2]
  exact ⟨r, rfl, hrle3, heq, hlock heq⟩

end Omega.Conclusion
