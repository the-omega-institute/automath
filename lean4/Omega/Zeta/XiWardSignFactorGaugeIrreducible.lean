import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-ward-sign-factor-gauge-irreducible`. -/
theorem paper_xi_ward_sign_factor_gauge_irreducible :
    ¬ ∃ ε : Nat → Int,
      (∀ n, ε n = 1 ∨ ε n = -1) ∧
        (∀ n, 2 ≤ n → ε (n + 2) * ε (n - 2) = 1) ∧
          (∀ n, 2 ≤ n →
            ((if (n / 2) % 2 = 0 then (1 : Int) else -1) *
                ε (n + 2) * ε (n - 2) =
              ε (n + 1) * ε (n - 1))) := by
  rintro ⟨ε, hsign, hstep, htwist⟩
  have hmul_eq {a b : Int} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
      (hab : a * b = 1) : a = b := by
    rcases ha with rfl | rfl
    · rcases hb with rfl | rfl
      · rfl
      · norm_num at hab
    · rcases hb with rfl | rfl
      · norm_num at hab
      · rfl
  have hperiod : ∀ m, ε (m + 4) = ε m := by
    intro m
    have hprod : ε (m + 4) * ε m = 1 := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep (m + 2) (by omega)
    exact hmul_eq (hsign (m + 4)) (hsign m) hprod
  have h46 : ε 6 * ε 2 = 1 := by
    simpa using hstep 4 (by norm_num)
  have h53 : ε 5 * ε 3 = 1 := by
    have htwist4 : ε 6 * ε 2 = ε 5 * ε 3 := by
      simpa using htwist 4 (by norm_num)
    rw [h46] at htwist4
    exact htwist4.symm
  have h84 : ε 8 * ε 4 = 1 := by
    simpa using hstep 6 (by norm_num)
  have h75 : ε 7 * ε 5 = -1 := by
    have htwist6 : (-1 : Int) * ε 8 * ε 4 = ε 7 * ε 5 := by
      simpa using htwist 6 (by norm_num)
    have hleft : (-1 : Int) * ε 8 * ε 4 = -1 := by
      rw [mul_assoc, h84]
      norm_num
    rw [hleft] at htwist6
    exact htwist6.symm
  have h35 : ε 3 * ε 5 = 1 := by
    rw [mul_comm]
    exact h53
  have h75_pos : ε 7 * ε 5 = 1 := by
    rw [hperiod 3]
    exact h35
  have hcontr : (1 : Int) = -1 := h75_pos.symm.trans h75
  norm_num at hcontr

end Omega.Zeta
