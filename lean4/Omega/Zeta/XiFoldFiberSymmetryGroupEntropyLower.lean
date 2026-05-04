import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete fiber-size data for the xi-fold symmetry entropy estimate. -/
structure xi_fold_fiber_symmetry_group_entropy_lower_data where
  fiberSizes : List ℕ
  N : ℕ
  M : ℕ
  sum_eq : fiberSizes.sum = N
  length_eq : fiberSizes.length = M

namespace xi_fold_fiber_symmetry_group_entropy_lower_data

/-- Product of the factorials of the individual fiber sizes. -/
def xi_fold_fiber_symmetry_group_entropy_lower_factorialProduct : List ℕ → ℕ
  | [] => 1
  | n :: ns => Nat.factorial n *
      xi_fold_fiber_symmetry_group_entropy_lower_factorialProduct ns

/-- The counted partition inequality: the product of fiber factorials divides the total
factorial. -/
lemma xi_fold_fiber_symmetry_group_entropy_lower_factorialProduct_dvd_sum_factorial :
    ∀ ns : List ℕ,
      xi_fold_fiber_symmetry_group_entropy_lower_factorialProduct ns ∣
        Nat.factorial ns.sum := by
  intro ns
  induction ns with
  | nil =>
      simp [xi_fold_fiber_symmetry_group_entropy_lower_factorialProduct]
  | cons n ns ih =>
      have hleft :
          Nat.factorial n * xi_fold_fiber_symmetry_group_entropy_lower_factorialProduct ns ∣
            Nat.factorial n * Nat.factorial ns.sum :=
        Nat.mul_dvd_mul_left _ ih
      have hright : Nat.factorial n * Nat.factorial ns.sum ∣ Nat.factorial (n + ns.sum) :=
        Nat.factorial_mul_factorial_dvd_factorial_add n ns.sum
      exact hleft.trans hright

/-- The visible symmetry group is no larger than the ambient permutation group. -/
def upper_bound (D : xi_fold_fiber_symmetry_group_entropy_lower_data) : Prop :=
  xi_fold_fiber_symmetry_group_entropy_lower_factorialProduct D.fiberSizes ≤ Nat.factorial D.N

/-- A real-valued gamma-style lower bound obtained by casting the counted partition inequality. -/
def gamma_lower_bound (D : xi_fold_fiber_symmetry_group_entropy_lower_data) : Prop :=
  (xi_fold_fiber_symmetry_group_entropy_lower_factorialProduct D.fiberSizes : ℝ) ≤
    (Nat.factorial D.N : ℝ)

/-- The nonnegative Stirling-scale deficit isolated from the factorial upper bound. -/
def stirling_lower_bound (D : xi_fold_fiber_symmetry_group_entropy_lower_data) : Prop :=
  0 ≤ (Nat.factorial D.N : ℝ) -
    (xi_fold_fiber_symmetry_group_entropy_lower_factorialProduct D.fiberSizes : ℝ)

/-- Fibonacci-scale growth for both the number of fibers and the total mass. -/
def fibonacci_scale_growth (D : xi_fold_fiber_symmetry_group_entropy_lower_data) : Prop :=
  D.N ≤ Nat.fib (D.N + 2) ∧ D.M ≤ Nat.fib (D.M + 2)

private lemma xi_fold_fiber_symmetry_group_entropy_lower_nat_le_fib_add_two (n : ℕ) :
    n ≤ Nat.fib (n + 2) := by
  by_cases hsmall : n ≤ 2
  · interval_cases n <;> native_decide
  · have hlarge : 5 ≤ n + 2 := by omega
    have hle : n + 2 ≤ Nat.fib (n + 2) := Nat.le_fib_self hlarge
    omega

private lemma xi_fold_fiber_symmetry_group_entropy_lower_upper
    (D : xi_fold_fiber_symmetry_group_entropy_lower_data) : D.upper_bound := by
  rw [upper_bound, ← D.sum_eq]
  exact Nat.le_of_dvd (Nat.factorial_pos _) <|
    xi_fold_fiber_symmetry_group_entropy_lower_factorialProduct_dvd_sum_factorial D.fiberSizes

/-- Paper label: `prop:xi-fold-fiber-symmetry-group-entropy-lower`. -/
theorem paper_xi_fold_fiber_symmetry_group_entropy_lower
    (D : xi_fold_fiber_symmetry_group_entropy_lower_data) :
    D.upper_bound ∧ D.gamma_lower_bound ∧ D.stirling_lower_bound ∧ D.fibonacci_scale_growth := by
  have hupper := xi_fold_fiber_symmetry_group_entropy_lower_upper D
  refine ⟨hupper, ?_, ?_, ?_⟩
  · rw [gamma_lower_bound]
    exact_mod_cast hupper
  · have hreal : (xi_fold_fiber_symmetry_group_entropy_lower_factorialProduct D.fiberSizes : ℝ) ≤
        (Nat.factorial D.N : ℝ) := by
      exact_mod_cast hupper
    exact sub_nonneg.mpr hreal
  · exact ⟨xi_fold_fiber_symmetry_group_entropy_lower_nat_le_fib_add_two D.N,
      xi_fold_fiber_symmetry_group_entropy_lower_nat_le_fib_add_two D.M⟩

end xi_fold_fiber_symmetry_group_entropy_lower_data

end Omega.Zeta
