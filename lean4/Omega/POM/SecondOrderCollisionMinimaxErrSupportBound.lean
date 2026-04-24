import Mathlib.Tactic
import Omega.Folding.Fiber
import Omega.POM.SecondOrderCollisionCommonBottleneck

open scoped BigOperators

namespace Omega.POM

/-- The finite-support closed form obtained by summing the common bottleneck contribution over the
support points. -/
noncomputable def secondOrderCollisionSupportMinimaxError {α : Type*} [Fintype α] (n : ℕ)
    (w : α → ℝ) : ℝ :=
  ∑ x, w x * commonBottleneckMinimaxError n (w x)

/-- The corresponding Yao lower-bound package on the same finite support. -/
noncomputable def secondOrderCollisionSupportYaoBound {α : Type*} [Fintype α] (n : ℕ)
    (w : α → ℝ) : ℝ :=
  ∑ x, w x * commonBottleneckYaoLowerBound n (w x)

private lemma scalar_support_bound_aux (n : ℕ) {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    (1 + (n : ℝ) * w) * (1 - w) ^ n ≤ 1 := by
  induction n with
  | zero =>
      simp
  | succ n ihn =>
      have h01 : 0 ≤ 1 - w := sub_nonneg.mpr hw1
      have hp_nonneg : 0 ≤ (1 - w) ^ n := pow_nonneg h01 n
      have hstep : (1 + ((n.succ : ℕ) : ℝ) * w) * (1 - w) ≤ 1 + (n : ℝ) * w := by
        have hsquare : 0 ≤ (((n.succ : ℕ) : ℝ)) * w ^ 2 := by positivity
        have hsucc : (((n.succ : ℕ) : ℝ)) = (n : ℝ) + 1 := by norm_num
        ring_nf
        nlinarith
      calc
        (1 + ((n.succ : ℕ) : ℝ) * w) * (1 - w) ^ n.succ
            = ((1 + ((n.succ : ℕ) : ℝ) * w) * (1 - w)) * (1 - w) ^ n := by
              rw [pow_succ]
              ring
        _ ≤ (1 + (n : ℝ) * w) * (1 - w) ^ n := by
              exact mul_le_mul_of_nonneg_right hstep hp_nonneg
        _ ≤ 1 := ihn

private lemma scalar_collision_term_le_inv (n : ℕ) (hn : 1 ≤ n) {w : ℝ} (hw0 : 0 ≤ w)
    (hw1 : w ≤ 1) : w * commonBottleneckMinimaxError n w ≤ 1 / (2 * n : ℝ) := by
  have h01 : 0 ≤ 1 - w := sub_nonneg.mpr hw1
  have hp_nonneg : 0 ≤ (1 - w) ^ n := pow_nonneg h01 n
  have hleft : (n : ℝ) * (w * (1 - w) ^ n) ≤ 1 := by
    calc
      (n : ℝ) * (w * (1 - w) ^ n) = ((n : ℝ) * w) * (1 - w) ^ n := by ring
      _ ≤ (1 + (n : ℝ) * w) * (1 - w) ^ n := by
            refine mul_le_mul_of_nonneg_right ?_ hp_nonneg
            nlinarith
      _ ≤ 1 := scalar_support_bound_aux n hw0 hw1
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hscalar : w * (1 - w) ^ n ≤ 1 / (n : ℝ) := by
    have hmul : (w * (1 - w) ^ n) * (n : ℝ) ≤ 1 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hleft
    exact (le_div_iff₀ hn_pos).2 hmul
  calc
    w * commonBottleneckMinimaxError n w = (1 / 2 : ℝ) * (w * (1 - w) ^ n) := by
      simp [commonBottleneckMinimaxError, mul_assoc, mul_comm]
    _ ≤ (1 / 2 : ℝ) * (1 / (n : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hscalar (by norm_num)
    _ = 1 / (2 * n : ℝ) := by
      field_simp [hn_pos.ne']

/-- Paper label: `cor:pom-second-order-collision-minimax-err-support-bound`. Summing the common
bottleneck closed form over the support and using `w (1 - w)^n ≤ 1 / n` gives the support-size
bound. Specializing `|X_m|` through `X.card_eq_fib` yields the Fold/Fibonacci form. -/
theorem paper_pom_second_order_collision_minimax_err_support_bound (m n : ℕ) (hn : 1 ≤ n)
    (w : Omega.X m → ℝ) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1) :
    secondOrderCollisionSupportMinimaxError n w = secondOrderCollisionSupportYaoBound n w ∧
      secondOrderCollisionSupportMinimaxError n w ≤ (Fintype.card (Omega.X m) : ℝ) / (2 * n) ∧
      secondOrderCollisionSupportMinimaxError n w ≤ (Nat.fib (m + 2) : ℝ) / (2 * n) := by
  have hEq :
      secondOrderCollisionSupportMinimaxError n w = secondOrderCollisionSupportYaoBound n w := by
    unfold secondOrderCollisionSupportMinimaxError secondOrderCollisionSupportYaoBound
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hpoint :=
      (paper_pom_second_order_collision_common_bottleneck n (w x) (hw0 x) (hw1 x)).1
    simp [hpoint]
  have hSupport :
      secondOrderCollisionSupportMinimaxError n w ≤ (Fintype.card (Omega.X m) : ℝ) / (2 * n) := by
    unfold secondOrderCollisionSupportMinimaxError
    calc
      ∑ x, w x * commonBottleneckMinimaxError n (w x) ≤ ∑ _x : Omega.X m, (1 / (2 * n : ℝ)) := by
        refine Finset.sum_le_sum ?_
        intro x hx
        exact scalar_collision_term_le_inv n hn (hw0 x) (hw1 x)
      _ = (Fintype.card (Omega.X m) : ℝ) / (2 * n) := by
        have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
        simp [Finset.card_univ]
        field_simp [hn0]
  have hFib :
      secondOrderCollisionSupportMinimaxError n w ≤ (Nat.fib (m + 2) : ℝ) / (2 * n) := by
    simpa [Omega.X.card_eq_fib] using hSupport
  exact ⟨hEq, hSupport, hFib⟩

end Omega.POM
