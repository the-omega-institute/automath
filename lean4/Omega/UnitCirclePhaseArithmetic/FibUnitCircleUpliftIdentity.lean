import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.Folding.FibonacciPolynomial

namespace Omega.UnitCirclePhaseArithmetic

/-- Lee--Yang/Joukowsky coordinate on the unit-circle parameter. -/
noncomputable def leyangJ (u : ℂ) : ℂ :=
  -u / (1 + u) ^ 2

noncomputable def fibPolyC (n : Nat) : Polynomial ℂ :=
  (Omega.fibPoly n).map (Int.castRingHom ℂ)

private theorem leyangJ_mul_sq (u : ℂ) (hum1 : u ≠ -1) :
    (1 + u) ^ 2 * leyangJ u = -u := by
  have hplus : 1 + u ≠ 0 := by
    intro h
    exact hum1 (eq_neg_of_add_eq_zero_right h)
  unfold leyangJ
  field_simp [hplus]

@[simp] private theorem fibPolyC_one : fibPolyC 1 = 1 := by
  simp [fibPolyC]

@[simp] private theorem fibPolyC_zero : fibPolyC 0 = 0 := by
  simp [fibPolyC]

@[simp] private theorem fibPolyC_two : fibPolyC 2 = 1 := by
  simp [fibPolyC]

@[simp] private theorem fibPolyC_succ_succ (n : Nat) :
    fibPolyC (n + 2) = fibPolyC (n + 1) + Polynomial.X * fibPolyC n := by
  simp [fibPolyC, Omega.fibPoly_succ_succ]

private theorem fib_uplift_step (u : ℂ) (hum1 : u ≠ -1) (k : Nat) :
    (1 + u) ^ (k + 2) * (fibPolyC (k + 3)).eval (leyangJ u) =
      (1 + u) * ((1 + u) ^ (k + 1) * (fibPolyC (k + 2)).eval (leyangJ u)) -
        u * ((1 + u) ^ k * (fibPolyC (k + 1)).eval (leyangJ u)) := by
  calc
    (1 + u) ^ (k + 2) * (fibPolyC (k + 3)).eval (leyangJ u)
        = (1 + u) ^ (k + 2) *
            ((fibPolyC (k + 2)).eval (leyangJ u) + leyangJ u * (fibPolyC (k + 1)).eval (leyangJ u)) := by
            simp [fibPolyC_succ_succ, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
    _ = (1 + u) * ((1 + u) ^ (k + 1) * (fibPolyC (k + 2)).eval (leyangJ u)) +
          ((1 + u) ^ 2 * leyangJ u) *
            ((1 + u) ^ k * (fibPolyC (k + 1)).eval (leyangJ u)) := by
          ring
    _ = (1 + u) * ((1 + u) ^ (k + 1) * (fibPolyC (k + 2)).eval (leyangJ u)) -
          u * ((1 + u) ^ k * (fibPolyC (k + 1)).eval (leyangJ u)) := by
          rw [leyangJ_mul_sq u hum1]
          ring

private theorem geom_sum_step (u : ℂ) (hu1 : u ≠ 1) (k : Nat) :
    (1 + u) * ((u ^ (k + 2) - 1) / (u - 1)) - u * ((u ^ (k + 1) - 1) / (u - 1)) =
      (u ^ (k + 3) - 1) / (u - 1) := by
  have hu_sub : u - 1 ≠ 0 := sub_ne_zero.mpr hu1
  field_simp [hu_sub]
  ring

/-- The Lee--Yang uplift of the Fibonacci polynomial agrees with the geometric sum on the unit
circle.
    thm:fib-unit-circle-uplift-identity -/
theorem paper_fib_unit_circle_uplift_identity (n : Nat) (hn : 1 ≤ n) (u : ℂ) (hu1 : u ≠ 1)
    (hum1 : u ≠ -1) :
    (1 + u) ^ (n - 1) * (fibPolyC n).eval (leyangJ u) = (u ^ n - 1) / (u - 1) := by
  let P : Nat → Prop := fun k =>
    (1 + u) ^ k * (fibPolyC (k + 1)).eval (leyangJ u) = (u ^ (k + 1) - 1) / (u - 1)
  have hP0 : P 0 := by
    have hu_sub : u - 1 ≠ 0 := sub_ne_zero.mpr hu1
    unfold P
    rw [eq_div_iff hu_sub]
    simp
  have hP1 : P 1 := by
    have hu_sub : u - 1 ≠ 0 := sub_ne_zero.mpr hu1
    unfold P
    rw [eq_div_iff hu_sub]
    simp
    ring_nf
  have hstep : ∀ k : Nat, P k → P (k + 1) → P (k + 2) := by
    intro k hk hk1
    unfold P at hk hk1 ⊢
    rw [fib_uplift_step u hum1 k, hk1, hk]
    exact geom_sum_step u hu1 k
  have hPair : ∀ k : Nat, P k ∧ P (k + 1) := by
    intro k
    induction k with
    | zero =>
        exact ⟨hP0, hP1⟩
    | succ k ih =>
        exact ⟨ih.2, hstep k ih.1 ih.2⟩
  have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hn
  simpa [P, hn'] using (hPair (n - 1)).1

end Omega.UnitCirclePhaseArithmetic
