import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-delta34-top-zeckendorf-implies-m6`. -/
theorem paper_conclusion_delta34_top_zeckendorf_implies_m6
    (m : ℕ) (hm : 6 ≤ m) (T Xbdry : ℕ → ℕ)
    (hT : T m = Nat.fib (m + 3)) (hX : Xbdry m = Nat.fib (m - 2)) :
    (T m = 34 ↔ m = 6) ∧ (m = 6 ↔ Xbdry m = 3) := by
  have hfib9 : Nat.fib 9 = 34 := by norm_num [Nat.fib]
  have hfib4 : Nat.fib 4 = 3 := by norm_num [Nat.fib]
  constructor
  · constructor
    · intro h
      have hfib : Nat.fib (m + 3) = Nat.fib 9 := by
        rw [← hT, h, hfib9]
      have hm_le : m + 3 ≤ 9 := by
        by_contra hle
        have hlt : 9 < m + 3 := Nat.lt_of_not_ge hle
        have hstrict : Nat.fib 9 < Nat.fib (m + 3) :=
          (Nat.fib_lt_fib (by decide : 2 ≤ 9)).2 hlt
        exact (lt_irrefl (Nat.fib 9)) (hfib.symm ▸ hstrict)
      omega
    · intro h
      subst h
      rw [hT]
      norm_num [Nat.fib]
  · constructor
    · intro h
      subst h
      rw [hX]
      norm_num [Nat.fib]
    · intro h
      have hfib : Nat.fib (m - 2) = Nat.fib 4 := by
        rw [← hX, h, hfib4]
      have hm_sub_ge : 4 ≤ m - 2 := by omega
      have hm_sub_le : m - 2 ≤ 4 := by
        by_contra hle
        have hlt : 4 < m - 2 := Nat.lt_of_not_ge hle
        have hstrict : Nat.fib 4 < Nat.fib (m - 2) :=
          (Nat.fib_lt_fib (by decide : 2 ≤ 4)).2 hlt
        exact (lt_irrefl (Nat.fib 4)) (hfib.symm ▸ hstrict)
      omega

end Omega.Conclusion
