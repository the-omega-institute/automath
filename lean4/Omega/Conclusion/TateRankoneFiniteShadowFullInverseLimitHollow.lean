import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-tate-rankone-finite-shadow-full-inverse-limit-hollow`. -/
theorem paper_conclusion_tate_rankone_finite_shadow_full_inverse_limit_hollow :
    ∀ n x y : Nat,
      1 ≤ n →
        x < 2 ^ n →
          y < 2 ^ n →
            ∃ v1 v2 k : Nat,
              (v1 % 2 = 1 ∨ v2 % 2 = 1) ∧
                (k * v1) % (2 ^ n) = x ∧ (k * v2) % (2 ^ n) = y := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro x y hn hx hy
      by_cases hzero : x = 0 ∧ y = 0
      · refine ⟨1, 0, 0, ?_, ?_, ?_⟩
        · left
          norm_num
        · simp [hzero.1]
        · simp [hzero.2]
      · by_cases hxodd : x % 2 = 1
        · refine ⟨x, y, 1, ?_, ?_, ?_⟩
          · exact Or.inl hxodd
          · simpa using Nat.mod_eq_of_lt hx
          · simpa using Nat.mod_eq_of_lt hy
        · by_cases hyodd : y % 2 = 1
          · refine ⟨x, y, 1, ?_, ?_, ?_⟩
            · exact Or.inr hyodd
            · simpa using Nat.mod_eq_of_lt hx
            · simpa using Nat.mod_eq_of_lt hy
          · have hxeven_mod : x % 2 = 0 := by
              rcases Nat.mod_two_eq_zero_or_one x with h | h
              · exact h
              · exact False.elim (hxodd h)
            have hyeven_mod : y % 2 = 0 := by
              rcases Nat.mod_two_eq_zero_or_one y with h | h
              · exact h
              · exact False.elim (hyodd h)
            cases n with
            | zero => omega
            | succ n' =>
                by_cases hn'zero : n' = 0
                · subst n'
                  have hx0 : x = 0 := by omega
                  have hy0 : y = 0 := by omega
                  exact False.elim (hzero ⟨hx0, hy0⟩)
                · have hn' : 1 ≤ n' := by omega
                  have hx_half : x / 2 < 2 ^ n' := by
                    have hx' : x < 2 * 2 ^ n' := by
                      simpa [pow_succ'] using hx
                    exact Nat.div_lt_of_lt_mul hx'
                  have hy_half : y / 2 < 2 ^ n' := by
                    have hy' : y < 2 * 2 ^ n' := by
                      simpa [pow_succ'] using hy
                    exact Nat.div_lt_of_lt_mul hy'
                  rcases ih n' (Nat.lt_succ_self n') (x / 2) (y / 2) hn' hx_half hy_half with
                    ⟨v1, v2, k, hprim, hxmod, hymod⟩
                  refine ⟨v1, v2, 2 * k, hprim, ?_, ?_⟩
                  · have hxeven : Even x := (Nat.even_iff).mpr hxeven_mod
                    calc
                      ((2 * k) * v1) % (2 ^ Nat.succ n') =
                          (2 * (k * v1)) % (2 * 2 ^ n') := by
                            simp [pow_succ', Nat.mul_assoc, Nat.mul_comm]
                      _ = 2 * ((k * v1) % (2 ^ n')) := by
                            rw [Nat.mul_mod_mul_left]
                      _ = 2 * (x / 2) := by rw [hxmod]
                      _ = x := Nat.two_mul_div_two_of_even hxeven
                  · have hyeven : Even y := (Nat.even_iff).mpr hyeven_mod
                    calc
                      ((2 * k) * v2) % (2 ^ Nat.succ n') =
                          (2 * (k * v2)) % (2 * 2 ^ n') := by
                            simp [pow_succ', Nat.mul_assoc, Nat.mul_comm]
                      _ = 2 * ((k * v2) % (2 ^ n')) := by
                            rw [Nat.mul_mod_mul_left]
                      _ = 2 * (y / 2) := by rw [hymod]
                      _ = y := Nat.two_mul_div_two_of_even hyeven

end Omega.Conclusion
