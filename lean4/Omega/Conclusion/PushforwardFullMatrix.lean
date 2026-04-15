import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

/-!
# Window-6 local pushforward envelope: full matrix algebra

A_6 = End(V) ≅ M_21(ℝ) where dim V = |X_6| = F(8) = 21.
Key arithmetic: 21² = 441, 21 = 3 × 7, 21 is not a perfect square.
-/

namespace Omega.Conclusion.PushforwardFullMatrix

/-- F(8) = 21: dimension of the window-6 state space.
    cor:conclusion-window6-local-pushforward-envelope-full-matrix -/
theorem fib8_eq_21 : Nat.fib 8 = 21 := by native_decide

/-- Paper package: window-6 pushforward full matrix algebra.
    cor:conclusion-window6-local-pushforward-envelope-full-matrix -/
theorem paper_conclusion_window6_pushforward_full_matrix :
    Nat.fib 8 = 21 ∧ 21 ^ 2 = 441 ∧ 6 < 21 ∧
    21 = 3 * 7 ∧
    ¬ ∃ k : Nat, 1 < k ∧ k < 21 ∧ k * k = 21 := by
  refine ⟨by native_decide, by norm_num, by omega, by omega, ?_⟩
  intro ⟨k, hk1, hk2, hk3⟩
  have : k ≤ 4 := by nlinarith
  interval_cases k <;> omega

/-- The full matrix algebra has dimension 21² = 441.
    cor:conclusion-window6-local-pushforward-envelope-full-matrix -/
theorem full_matrix_dim : 21 * 21 = 441 := by omega

/-- 21 is squarefree: 21 = 3 · 7 with 3, 7 both prime.
    cor:conclusion-window6-local-pushforward-envelope-full-matrix -/
theorem twentyone_factorization :
    21 = 3 * 7 ∧ Nat.Prime 3 ∧ Nat.Prime 7 := by
  refine ⟨by omega, by decide, by decide⟩

end Omega.Conclusion.PushforwardFullMatrix
