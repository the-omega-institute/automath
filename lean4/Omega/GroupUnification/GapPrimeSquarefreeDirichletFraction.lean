import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

namespace Omega.GroupUnification

open Finset
open scoped BigOperators

/-- Concrete exponent data for the gap-squarefree prime Dirichlet truncations.  We work with
an integer exponent `s ≥ 2`, so every prime weight is a positive real number. -/
structure xi_gap_prime_squarefree_dirichlet_fraction_data where
  s : ℕ
  hs : 2 ≤ s

noncomputable def xi_gap_prime_squarefree_dirichlet_fraction_prime_weight
    (D : xi_gap_prime_squarefree_dirichlet_fraction_data) (n : ℕ) : ℝ :=
  (((Nat.nth Nat.Prime n : ℕ) : ℝ) ^ D.s)⁻¹

noncomputable def xi_gap_prime_squarefree_dirichlet_fraction_truncation
    (D : xi_gap_prime_squarefree_dirichlet_fraction_data) : ℕ → ℝ
  | 0 => 1
  | 1 => 1 + xi_gap_prime_squarefree_dirichlet_fraction_prime_weight D 0
  | n + 2 =>
      xi_gap_prime_squarefree_dirichlet_fraction_truncation D (n + 1) +
        xi_gap_prime_squarefree_dirichlet_fraction_prime_weight D (n + 1) *
          xi_gap_prime_squarefree_dirichlet_fraction_truncation D n

noncomputable def xi_gap_prime_squarefree_dirichlet_fraction_ratio
    (D : xi_gap_prime_squarefree_dirichlet_fraction_data) : ℕ → ℝ
  | 0 => 1
  | n + 1 =>
      xi_gap_prime_squarefree_dirichlet_fraction_truncation D (n + 1) /
        xi_gap_prime_squarefree_dirichlet_fraction_truncation D n

noncomputable def xi_gap_prime_squarefree_dirichlet_fraction_euler_upper
    (D : xi_gap_prime_squarefree_dirichlet_fraction_data) (n : ℕ) : ℝ :=
  Finset.prod (Finset.range n)
    (fun i => 1 + xi_gap_prime_squarefree_dirichlet_fraction_prime_weight D i)

def xi_gap_prime_squarefree_dirichlet_fraction_spec
    (D : xi_gap_prime_squarefree_dirichlet_fraction_data) : Prop :=
  xi_gap_prime_squarefree_dirichlet_fraction_truncation D 0 = 1 ∧
    xi_gap_prime_squarefree_dirichlet_fraction_truncation D 1 =
      1 + xi_gap_prime_squarefree_dirichlet_fraction_prime_weight D 0 ∧
    (∀ n,
      xi_gap_prime_squarefree_dirichlet_fraction_truncation D (n + 2) =
        xi_gap_prime_squarefree_dirichlet_fraction_truncation D (n + 1) +
          xi_gap_prime_squarefree_dirichlet_fraction_prime_weight D (n + 1) *
            xi_gap_prime_squarefree_dirichlet_fraction_truncation D n) ∧
    (∀ n, 0 < xi_gap_prime_squarefree_dirichlet_fraction_truncation D n) ∧
    Monotone (xi_gap_prime_squarefree_dirichlet_fraction_truncation D) ∧
    (∀ n,
      xi_gap_prime_squarefree_dirichlet_fraction_truncation D n ≤
        xi_gap_prime_squarefree_dirichlet_fraction_euler_upper D n) ∧
    xi_gap_prime_squarefree_dirichlet_fraction_ratio D 1 =
      1 + xi_gap_prime_squarefree_dirichlet_fraction_prime_weight D 0 ∧
    (∀ n,
      0 < xi_gap_prime_squarefree_dirichlet_fraction_ratio D (n + 1)) ∧
    (∀ n,
      xi_gap_prime_squarefree_dirichlet_fraction_ratio D (n + 2) =
        1 + xi_gap_prime_squarefree_dirichlet_fraction_prime_weight D (n + 1) /
          xi_gap_prime_squarefree_dirichlet_fraction_ratio D (n + 1))

private lemma xi_gap_prime_squarefree_dirichlet_fraction_prime_weight_pos
    (D : xi_gap_prime_squarefree_dirichlet_fraction_data) (n : ℕ) :
    0 < xi_gap_prime_squarefree_dirichlet_fraction_prime_weight D n := by
  unfold xi_gap_prime_squarefree_dirichlet_fraction_prime_weight
  exact inv_pos.mpr <| pow_pos (by exact_mod_cast (Nat.Prime.pos (Nat.prime_nth_prime n))) _

private lemma xi_gap_prime_squarefree_dirichlet_fraction_euler_upper_pos
    (D : xi_gap_prime_squarefree_dirichlet_fraction_data) (n : ℕ) :
    0 < xi_gap_prime_squarefree_dirichlet_fraction_euler_upper D n := by
  induction n with
  | zero =>
      simp [xi_gap_prime_squarefree_dirichlet_fraction_euler_upper]
  | succ n ihn =>
      simp [xi_gap_prime_squarefree_dirichlet_fraction_euler_upper, Finset.prod_range_succ]
      have hw := xi_gap_prime_squarefree_dirichlet_fraction_prime_weight_pos D n
      exact mul_pos ihn (by linarith)

private lemma xi_gap_prime_squarefree_dirichlet_fraction_euler_upper_succ
    (D : xi_gap_prime_squarefree_dirichlet_fraction_data) (n : ℕ) :
    xi_gap_prime_squarefree_dirichlet_fraction_euler_upper D (n + 1) =
      xi_gap_prime_squarefree_dirichlet_fraction_euler_upper D n *
        (1 + xi_gap_prime_squarefree_dirichlet_fraction_prime_weight D n) := by
  simp [xi_gap_prime_squarefree_dirichlet_fraction_euler_upper, Finset.prod_range_succ]

private lemma xi_gap_prime_squarefree_dirichlet_fraction_euler_upper_le_succ
    (D : xi_gap_prime_squarefree_dirichlet_fraction_data) (n : ℕ) :
    xi_gap_prime_squarefree_dirichlet_fraction_euler_upper D n ≤
      xi_gap_prime_squarefree_dirichlet_fraction_euler_upper D (n + 1) := by
  rw [xi_gap_prime_squarefree_dirichlet_fraction_euler_upper_succ]
  have hpos : 0 ≤ xi_gap_prime_squarefree_dirichlet_fraction_euler_upper D n := by
    exact (xi_gap_prime_squarefree_dirichlet_fraction_euler_upper_pos D n).le
  have hw : 0 ≤ xi_gap_prime_squarefree_dirichlet_fraction_prime_weight D n := by
    exact (xi_gap_prime_squarefree_dirichlet_fraction_prime_weight_pos D n).le
  nlinarith

private lemma xi_gap_prime_squarefree_dirichlet_fraction_truncation_pos
    (D : xi_gap_prime_squarefree_dirichlet_fraction_data) :
    ∀ n, 0 < xi_gap_prime_squarefree_dirichlet_fraction_truncation D n
  | 0 => by
      simp [xi_gap_prime_squarefree_dirichlet_fraction_truncation]
  | 1 => by
      simpa [xi_gap_prime_squarefree_dirichlet_fraction_truncation] using
        add_pos_of_pos_of_nonneg (show (0 : ℝ) < 1 by norm_num)
          (xi_gap_prime_squarefree_dirichlet_fraction_prime_weight_pos D 0).le
  | n + 2 => by
      have hz₁ := xi_gap_prime_squarefree_dirichlet_fraction_truncation_pos D (n + 1)
      have hz₀ := xi_gap_prime_squarefree_dirichlet_fraction_truncation_pos D n
      have hw := xi_gap_prime_squarefree_dirichlet_fraction_prime_weight_pos D (n + 1)
      simpa [xi_gap_prime_squarefree_dirichlet_fraction_truncation] using
        add_pos hz₁ (mul_pos hw hz₀)

private lemma xi_gap_prime_squarefree_dirichlet_fraction_truncation_le_succ
    (D : xi_gap_prime_squarefree_dirichlet_fraction_data) :
    ∀ n,
      xi_gap_prime_squarefree_dirichlet_fraction_truncation D n ≤
        xi_gap_prime_squarefree_dirichlet_fraction_truncation D (n + 1)
  | 0 => by
      simp [xi_gap_prime_squarefree_dirichlet_fraction_truncation,
        (xi_gap_prime_squarefree_dirichlet_fraction_prime_weight_pos D 0).le]
  | n + 1 => by
      have hnonneg :
          0 ≤
            xi_gap_prime_squarefree_dirichlet_fraction_prime_weight D (n + 1) *
              xi_gap_prime_squarefree_dirichlet_fraction_truncation D n := by
        exact mul_nonneg
          (xi_gap_prime_squarefree_dirichlet_fraction_prime_weight_pos D (n + 1)).le
          (xi_gap_prime_squarefree_dirichlet_fraction_truncation_pos D n).le
      simpa [xi_gap_prime_squarefree_dirichlet_fraction_truncation] using
        (show
          xi_gap_prime_squarefree_dirichlet_fraction_truncation D (n + 1) ≤
            xi_gap_prime_squarefree_dirichlet_fraction_truncation D (n + 1) +
              xi_gap_prime_squarefree_dirichlet_fraction_prime_weight D (n + 1) *
                xi_gap_prime_squarefree_dirichlet_fraction_truncation D n from
          le_add_of_nonneg_right hnonneg)

private lemma xi_gap_prime_squarefree_dirichlet_fraction_truncation_monotone
    (D : xi_gap_prime_squarefree_dirichlet_fraction_data) :
    Monotone (xi_gap_prime_squarefree_dirichlet_fraction_truncation D) := by
  intro a b hab
  induction hab with
  | refl => exact le_rfl
  | @step b hb ih =>
      exact le_trans ih (xi_gap_prime_squarefree_dirichlet_fraction_truncation_le_succ D b)

private lemma xi_gap_prime_squarefree_dirichlet_fraction_truncation_le_euler_upper
    (D : xi_gap_prime_squarefree_dirichlet_fraction_data) :
    ∀ n,
      xi_gap_prime_squarefree_dirichlet_fraction_truncation D n ≤
        xi_gap_prime_squarefree_dirichlet_fraction_euler_upper D n
  | 0 => by
      simp [xi_gap_prime_squarefree_dirichlet_fraction_truncation,
        xi_gap_prime_squarefree_dirichlet_fraction_euler_upper]
  | 1 => by
      simp [xi_gap_prime_squarefree_dirichlet_fraction_truncation,
        xi_gap_prime_squarefree_dirichlet_fraction_euler_upper,
        xi_gap_prime_squarefree_dirichlet_fraction_prime_weight]
  | n + 2 => by
      have ih₁ := xi_gap_prime_squarefree_dirichlet_fraction_truncation_le_euler_upper D (n + 1)
      have ih₂ := xi_gap_prime_squarefree_dirichlet_fraction_truncation_le_euler_upper D n
      have hmono :=
        xi_gap_prime_squarefree_dirichlet_fraction_euler_upper_le_succ D n
      have hw :
          0 ≤ xi_gap_prime_squarefree_dirichlet_fraction_prime_weight D (n + 1) := by
        exact (xi_gap_prime_squarefree_dirichlet_fraction_prime_weight_pos D (n + 1)).le
      calc
        xi_gap_prime_squarefree_dirichlet_fraction_truncation D (n + 2)
            = xi_gap_prime_squarefree_dirichlet_fraction_truncation D (n + 1) +
                xi_gap_prime_squarefree_dirichlet_fraction_prime_weight D (n + 1) *
                  xi_gap_prime_squarefree_dirichlet_fraction_truncation D n := by
                  simp [xi_gap_prime_squarefree_dirichlet_fraction_truncation]
        _ ≤ xi_gap_prime_squarefree_dirichlet_fraction_euler_upper D (n + 1) +
              xi_gap_prime_squarefree_dirichlet_fraction_prime_weight D (n + 1) *
                xi_gap_prime_squarefree_dirichlet_fraction_euler_upper D n := by
              exact add_le_add ih₁ (mul_le_mul_of_nonneg_left ih₂ hw)
        _ ≤ xi_gap_prime_squarefree_dirichlet_fraction_euler_upper D (n + 1) +
              xi_gap_prime_squarefree_dirichlet_fraction_prime_weight D (n + 1) *
                xi_gap_prime_squarefree_dirichlet_fraction_euler_upper D (n + 1) := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_left (mul_le_mul_of_nonneg_left hmono hw)
                  (xi_gap_prime_squarefree_dirichlet_fraction_euler_upper D (n + 1))
        _ = xi_gap_prime_squarefree_dirichlet_fraction_euler_upper D (n + 2) := by
              rw [xi_gap_prime_squarefree_dirichlet_fraction_euler_upper_succ D (n + 1)]
              ring

private lemma xi_gap_prime_squarefree_dirichlet_fraction_ratio_pos
    (D : xi_gap_prime_squarefree_dirichlet_fraction_data) (n : ℕ) :
    0 < xi_gap_prime_squarefree_dirichlet_fraction_ratio D (n + 1) := by
  unfold xi_gap_prime_squarefree_dirichlet_fraction_ratio
  exact div_pos
    (xi_gap_prime_squarefree_dirichlet_fraction_truncation_pos D (n + 1))
    (xi_gap_prime_squarefree_dirichlet_fraction_truncation_pos D n)

private lemma xi_gap_prime_squarefree_dirichlet_fraction_ratio_recursion
    (D : xi_gap_prime_squarefree_dirichlet_fraction_data) (n : ℕ) :
    xi_gap_prime_squarefree_dirichlet_fraction_ratio D (n + 2) =
      1 + xi_gap_prime_squarefree_dirichlet_fraction_prime_weight D (n + 1) /
        xi_gap_prime_squarefree_dirichlet_fraction_ratio D (n + 1) := by
  have hz₀ :
      xi_gap_prime_squarefree_dirichlet_fraction_truncation D n ≠ 0 := by
    exact ne_of_gt (xi_gap_prime_squarefree_dirichlet_fraction_truncation_pos D n)
  have hz₁ :
      xi_gap_prime_squarefree_dirichlet_fraction_truncation D (n + 1) ≠ 0 := by
    exact ne_of_gt (xi_gap_prime_squarefree_dirichlet_fraction_truncation_pos D (n + 1))
  unfold xi_gap_prime_squarefree_dirichlet_fraction_ratio
  simp [xi_gap_prime_squarefree_dirichlet_fraction_truncation]
  field_simp [hz₀, hz₁]

/-- Finite gap-squarefree truncations satisfy the Fibonacci-type recurrence, are positive and
monotone, are dominated by the unrestricted Euler products, and their successive ratios obey the
continued-fraction recursion.
    thm:xi-gap-prime-squarefree-dirichlet-fraction -/
theorem paper_xi_gap_prime_squarefree_dirichlet_fraction
    (D : xi_gap_prime_squarefree_dirichlet_fraction_data) :
    xi_gap_prime_squarefree_dirichlet_fraction_spec D := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    simp [xi_gap_prime_squarefree_dirichlet_fraction_truncation]
  · exact xi_gap_prime_squarefree_dirichlet_fraction_truncation_pos D
  · exact xi_gap_prime_squarefree_dirichlet_fraction_truncation_monotone D
  · exact xi_gap_prime_squarefree_dirichlet_fraction_truncation_le_euler_upper D
  · unfold xi_gap_prime_squarefree_dirichlet_fraction_ratio
    simp [xi_gap_prime_squarefree_dirichlet_fraction_truncation]
  · intro n
    exact xi_gap_prime_squarefree_dirichlet_fraction_ratio_pos D n
  · intro n
    exact xi_gap_prime_squarefree_dirichlet_fraction_ratio_recursion D n

end Omega.GroupUnification
